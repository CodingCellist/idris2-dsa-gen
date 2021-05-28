module DSAGen.DSL

import Data.List
import Data.String.Extra

%default total

||| A label is a string labelling the thing it is associated with.
data Label : Type where
  MkLabel : (label : String) -> Label

Show Label where
  show (MkLabel label) = label

%name Label l, l1, l2, l3

||| A state in a DSA has a label.
data State : Type where
  MkState : Label -> State

Show State where
  show (MkState l) = show l

||| A dependent result has an identifier (name of the result) and a state it
||| goes to.
data DepRes : Type where
  MkDepRes : (resName : String) -> (to : State) -> DepRes

getResName : DepRes -> String
getResName (MkDepRes resName _) = resName

Show DepRes where
  show (MkDepRes resName to) = "(" ++ resName ++ ") => " ++ show to

||| An edge is either a regular action from s1 to s2, or a dependent action
||| which has a label and a list of dependent results and the state they go to.
data Edge : Type where
  RegAction : Label -> (from : State) -> (to : State) -> Edge
  DepAction : Label
            -> (from : State)
            -> (depTo : List DepRes)
            -> {auto 0 ok : NonEmpty depTo}
            -> Edge

Show Edge where
  show (RegAction l from to) =
    show from ++  " --" ++ show l ++ "--> " ++ show to
  show (DepAction l from depTo) =
    show from ++ " --" ++ show l ++ "-->{ " ++ show depTo

||| Given a list of edges, separate into a list of only regular edges and
||| only dependent edges respectively.
sortEdges : (es : List Edge)
          -> {auto 0 ok : NonEmpty es}
          -> (List Edge, List Edge)
sortEdges [] impossible

sortEdges (e@(RegAction l _ _) :: []) = ([e], [])

sortEdges (de@(DepAction l _ _) :: []) = ([], [de])

sortEdges (e@(RegAction l _ _) :: (e1 :: es)) =
  let (regs, deps) = sortEdges (e1 :: es)
  in (e :: regs , deps)

sortEdges (de@(DepAction l _ _) :: (e1 :: es)) =
  let (regs, deps) = sortEdges (e1 :: es)
  in (regs , de :: deps)


extractDepStates : List Edge -> List (List DepRes)
extractDepStates [] = []
extractDepStates ((RegAction l _ _) :: es) =
  assert_total $ idris_crash "Got a RegAction in extractDepStates."
extractDepStates ((DepAction l _ depTo) :: es) =
  depTo :: extractDepStates es

||| A DSA is simply a list of states and edges/actions.
data DSA : Type where
  MkDSA : (states : List State)
        -> (edges : List Edge)
        -> {auto 0 ok : NonEmpty edges}
        -> DSA

tabWidth : Nat
tabWidth = 2

indent : String
indent = pack $ replicate tabWidth ' '

-- `Pure` is always defined in the same way
dsaPure : String
dsaPure = indent ++ "Pure : (res : ty) -> Cmd ty (state_fn res) state_fn"

-- Bind is always defined in the same way
dsaBind : String
dsaBind =
  indent
  ++ "(>>=) : Cmd a state1 state2_fn" ++ "\n" ++ indent
  ++ "      -> ((res : a) -> Cmd b (state2_fn res) state3_fn)" ++ "\n" ++ indent
  ++ "      -> Cmd b state1 state3_fn"

||| Naïvely generate Idris source by magically outputting the right string.
||| EXTREMELY FRAGILE!
export
unsafeGenIdris : DSA -> String
unsafeGenIdris (MkDSA states edges) =
  let
    -- first: create a data-type containing every state
    statesStr = genStates states
    -- then, separate the regular from the dependent actions
    (regs, deps) = sortEdges edges
    -- second: create a data-type for each of the dependent results, with
    --         constructors for each alternative
    depResStr = lineSeparate $ handleDepStates deps
    -- third: define `Cmd` data-type containing all the transitions as
    -- constructors
    cmdDataStr = genCmds regs deps
  in
    lineSeparate ["-- UNSAFELY GENERATED! --"
                 , statesStr
                 , depResStr
                 , cmdDataStr
                 , dsaPure
                 , dsaBind
                 ]
  where
    -- Data.String.Extra.join
    lineSeparate : List String -> String
    lineSeparate xs = join "\n\n" xs

    -- generate a `State` data-type whose constructors are each of the possible
    -- states in the DSA
    genStates : List State -> String
    genStates states =
      "data State = " ++ (join " | " $ map show states)

    -- generate a data-type for each DepAction's result type, containing
    -- constructors for each of the 
    handleDepStates : List Edge -> List String
    handleDepStates [] = []
    handleDepStates ((RegAction _ _ _) :: es) =
      assert_total $ idris_crash "Got a RegAction in handleDepStates."
    handleDepStates ((DepAction l from depTo) :: es) =
      ("data " ++ show l ++ "Res = " ++ (join " | " $ map getResName depTo))
      :: handleDepStates es

    -- regular commands have a name, and always use `const <to>` as their
    -- `state_fn`
    genRegCmds : List Edge -> String
    genRegCmds [] = ""
    genRegCmds ((RegAction l from to) :: es) =
      indent
      ++ show l ++ " : Cmd () " ++ show from ++ " (const " ++ show to ++ ")"
      ++ "\n" ++ genRegCmds es
    genRegCmds ((DepAction _ _ _) :: es) =
      assert_total $ idris_crash "Got a DepAction in genRegCmds."

    -- cases in a dependent state function have the form
    -- <ResName> => <destState>
    genDepStateCases : List DepRes -> List String
    genDepStateCases [] = []
    genDepStateCases ((MkDepRes resName to) :: es) =
      (resName ++ " => " ++ show to) :: genDepStateCases es

    -- dependent commands occur **exactly once** per labelled transition, the
    -- changing step is that their `state_fn` is an anonymous function to
    -- various states
    genDepCmds : List Edge -> String
    genDepCmds [] = ""
    genDepCmds ((RegAction _ _ _) :: es) =
      assert_total $ idris_crash "Got a RegAction in genDepCmds"
    genDepCmds ((DepAction l from depTo) :: es) =
      indent
      ++ show l ++ " : Cmd " ++ show l ++ "Res " ++ show from
      ++ " (\\depRes => case depRes of " ++ (join "; " $ genDepStateCases depTo)
      ++ ")\n" ++ genDepCmds es

    -- generate the `Cmd` data-type, by generating the regular commands first,
    -- followed by the dependent commands
    genCmds : (regs : List Edge) -> (deps : List Edge) -> String
    genCmds regs deps =
      "data Cmd : (ty : Type) -> State -> (ty -> State) -> Type where"
      ++ "\n"
      ++ genRegCmds regs
      ++ genDepCmds deps

-----------------------------
-- EXAMPLE DSA (TDD Ch.14) --
-----------------------------

any : State
any = MkState (MkLabel "state")

atm_s1 : State
atm_s1 = MkState (MkLabel "Ready")

atm_s2 : State
atm_s2 = MkState (MkLabel "CardInserted")

atm_s3 : State
atm_s3 = MkState (MkLabel "Session")

s1s2 : Edge
s1s2 = RegAction (MkLabel "InsertCard") atm_s1 atm_s2

s2s2 : Edge
s2s2 = RegAction (MkLabel "GetPIN") atm_s2 atm_s2

s2dep : Edge
s2dep = DepAction (MkLabel "CheckPin")
                  atm_s2
                  [MkDepRes "Incorrect" atm_s2, MkDepRes "Correct" atm_s3]

s3s3 : Edge
s3s3 = RegAction (MkLabel "Dispense") atm_s3 atm_s3

-- NOT QUITE CORRECT:
anyS1 : Edge
anyS1 = RegAction (MkLabel "EjectCard") any atm_s1

-- s2s1 : Edge
-- s2s1 = RegAction (MkLabel "EjectCard") atm_s2 atm_s1
-- 
-- s3s1 : Edge
-- s3s1 = RegAction (MkLabel "EjectCard") atm_s3 atm_s1

export
atm : DSA
atm = MkDSA [atm_s1, atm_s2, atm_s3]
            [s1s2, s2s2, s2dep, s3s3, anyS1]
--            [s1s2, s2s1, s2s2, s2dep, s3s3, s3s1]

