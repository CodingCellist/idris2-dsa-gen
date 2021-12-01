module DSAGen.DSL2

import Data.List
import Data.String.Extra

%default total

||| A label is a string labelling the thing it is associated with.
public export
data Label : Type where
  MkLabel : (label : String) -> Label

||| Two `Label`s are equal iff their internal strings are equal.
export
Eq Label where
  (==) (MkLabel l1) (MkLabel l2) = l1 == l2

export
Show Label where
  show (MkLabel label) = label

%name Label l, l1, l2, l3

||| A state in a DSA has a label.
public export
data State : Type where
  MkState : Label -> State

||| Two `State`s are equal iff their `Label`s are equal.
export
Eq State where
  (==) (MkState l1) (MkState l2) = l1 == l2

Show State where
  show (MkState l) = show l

||| Given a name, create a new `State` with the given name as a `Label`.
|||
||| @ name the label for the state
export
newState : (name : String) -> State
newState = MkState . MkLabel

||| A dependent result has an identifier (name of the result) and a state it
||| goes to.
public export
data DepRes : Type where
  MkDepRes : (resName : String) -> (to : State) -> DepRes

||| Extract the name of the result that the given `DepRes` depends on.
getResName : DepRes -> String
getResName (MkDepRes resName _) = resName

||| Two dependent results are equal iff their result-names are equal and their
||| destinations are equal.
export
Eq DepRes where
  (==) (MkDepRes resName1 t1) (MkDepRes resName2 t2) =
    resName1 == resName2 && t1 == t2

Show DepRes where
  show (MkDepRes resName to) = "(" ++ resName ++ ") => " ++ show to

--- ||| An edge is either a regular action from s1 to s2, or a dependent action
--- ||| which has a label and a list of dependent results and the state they go to.
--- public export
--- data Edge : Type where
---   ||| A non-dependent transition between two states.
---   RegAction : (name : Label) -> (from : State) -> (to : State) -> Edge
---   ||| A dependent transition from a state to at least one other state.
---   DepAction :  (name  : Label)
---             -> (from  : State)
---             -> (depTo : List DepRes)
--- --            -> {auto 0 ok : NonEmpty depTo}
---             -> Edge
--- 
--- ||| Extract the starting `State` of an `Edge`.
--- export
--- from : Edge -> State
--- from (RegAction _ f _) = f
--- from (DepAction _ f _) = f
--- 
--- ||| Extract the name of the given `Edge`.
--- export
--- name : Edge -> Label
--- name (RegAction n _ _) = n
--- name (DepAction n _ _) = n
--- 
--- ||| Extract the `DepRes` of the given `Edge`.
--- ||| /!\ Crashes if given a `RegAction` /!\
--- export
--- depTo : Edge -> List DepRes
--- depTo (RegAction _ _ _) =
---   assert_total $ idris_crash "Got a RegAction in depTo."
--- depTo (DepAction _ _ dt) = dt
--- 
--- ||| Two `Edge`s are equal iff their labels, source, and destination(s) are
--- ||| equal.
--- export
--- Eq Edge where
---   (==) (RegAction l1 f1 t1) (RegAction l2 f2 t2) =
---     l1 == l2 && f1 == f2 && t1 == t2
--- 
---   (==) (DepAction l1 f1 t1) (DepAction l2 f2 t2) =
---     l1 == l2 && f1 == f2 && t1 == t2
--- 
---   (==) _ _ = False
--- 
--- Show Edge where
---   show (RegAction l from to) =
---     show from ++  " --" ++ show l ++ "--> " ++ show to
---   show (DepAction l from depTo) =
---     show from ++ " --" ++ show l ++ "-->{ " ++ show depTo
--- 
--- ||| Returns `True` iff the given `Edge` is a dependent action.
--- export
--- isDepAction : Edge -> Bool
--- isDepAction (RegAction _ _ _) = False
--- isDepAction (DepAction _ _ _) = True
--- 
--- ||| Return `True` iff the given `Edge` is a regular action.
--- export
--- isRegAction : Edge -> Bool
--- isRegAction = not . isDepAction

public export
data RegEdge : Type where
  MkRegEdge :  (name : Label)
            -> (from : State)
            -> (to   : State)
            -> RegEdge

-- RegEdge projections
namespace RegEdge
  ||| Get the `RegEdge`'s "name".
  export
  name : RegEdge -> Label
  name (MkRegEdge n _ _) = n

  ||| Get the `RegEdge`'s "from" `State`.
  export
  from : RegEdge -> State
  from (MkRegEdge _ f _) = f

  ||| Get the `RegEdge`'s "to" `State`.
  export
  to : RegEdge -> State
  to (MkRegEdge _ _ t) = t

export
Eq RegEdge where
  (==) (MkRegEdge n1 f1 t1) (MkRegEdge n2 f2 t2) =
    n1 == n2 && f1 == f2 && t1 == t2

export
Show RegEdge where
  show (MkRegEdge name from to) =
    show from ++ " --" ++ show name ++ "--> " ++ show to

public export
data DepEdge : Type where
  MkDepEdge :  (name  : Label)
            -> (from  : State)
            -> (depTo : List DepRes)
            -> DepEdge

-- DepEdge projections
namespace DepEdge
  ||| Get the `DepEdge`'s "name".
  export
  name : DepEdge -> Label
  name (MkDepEdge n _ _) = n

  ||| Get the `DepEdge`'s "from" state.
  export
  from : DepEdge -> State
  from (MkDepEdge _ f _) = f

  ||| Get the `DepEdge`'s list of `DepRes` dependent results (i.e. the states
  ||| the `DepEdge` can dependently transition to).
  export
  depTo : DepEdge -> List DepRes
  depTo (MkDepEdge _ _ dt) = dt

export
Eq DepEdge where
  (==) (MkDepEdge n1 f1 dt1) (MkDepEdge n2 f2 dt2) =
    n1 == n2 && f1 == f2 && dt1 == dt2

export
Show DepEdge where
  show (MkDepEdge name from depTo) =
    show from ++ " --" ++ show name ++ "-->{ " ++ show depTo ++ " }"

--- ||| Given a list of edges, separate into a list of only regular edges and
--- ||| only dependent edges respectively.
--- sortEdges : (es : List Edge)
--- --          -> {auto 0 ok : NonEmpty es}
---           -> (List Edge, List Edge)
--- --sortEdges [] impossible
--- sortEdges [] = ([], [])
--- 
--- sortEdges (e@(RegAction l _ _) :: []) = ([e], [])
--- 
--- sortEdges (de@(DepAction l _ _) :: []) = ([], [de])
--- 
--- sortEdges (e@(RegAction l _ _) :: (e1 :: es)) =
---   let (regs, deps) = sortEdges (e1 :: es)
---   in (e :: regs , deps)
--- 
--- sortEdges (de@(DepAction l _ _) :: (e1 :: es)) =
---   let (regs, deps) = sortEdges (e1 :: es)
---   in (regs , de :: deps)
--- 
--- ||| Extract all the `DepRes`'s from the given list of `Edge`s.
--- ||| /!\ Crashes if the list contains a `RegAction` /!\
--- export
--- extractDepStates : List Edge -> List (List DepRes)
--- extractDepStates [] = []
--- extractDepStates (e :: es) = depTo e :: extractDepStates es
--- --extractDepStates ((RegAction l _ _) :: es) =
--- --  assert_total $ idris_crash "Got a RegAction in extractDepStates."
--- --extractDepStates ((DepAction l _ depTo) :: es) =
--- --  depTo :: extractDepStates es
--- 
--- ||| A DSA is simply a list of states and edges/actions.
--- public export
--- data DSA : Type where
---   MkDSA :  (states : List State)
---         -> (edges : List Edge)
--- --        -> {auto 0 ok : NonEmpty edges}
---         -> DSA

public export
data DSA2 : Type where
  MkDSA2 :  (dsaName  : String)
         -> (states   : List State)
         -> (regEdges : List RegEdge)
         -> (depEdges : List DepEdge)
         -> DSA2

||| If `a` describes a Dependent State Automaton, there must be a mapping from
||| `a` to `DSA`.
public export
interface DSA2Desc a where
  toDSA2 : a -> DSA2


-----------------------------
-- MAGIC STRING GENERATION --
-----------------------------

tabWidth : Nat
tabWidth = 2

indent : String
indent = pack $ replicate tabWidth ' '

--- -- `Pure` is always defined in the same way
--- dsaPure : String
--- dsaPure = indent ++ "Pure : (res : ty) -> Cmd ty (state_fn res) state_fn"
--- 
--- -- Bind is always defined in the same way
--- dsaBind : String
--- dsaBind =
---   indent
---   ++ "(>>=) : Cmd a state1 state2_fn" ++ "\n" ++ indent
---   ++ "      -> ((res : a) -> Cmd b (state2_fn res) state3_fn)" ++ "\n" ++ indent
---   ++ "      -> Cmd b state1 state3_fn"

||| `Pure` is always defined the same way, but requires the name of the DSA to
||| make sense (because the name is part of the name of the `Cmd` type)
dsa2Pure : DSA2 -> String
dsa2Pure (MkDSA2 dsaName  _ _ _) =
  indent ++ "Pure : (res : ty) -> " ++ dsaName  ++ "Cmd ty (state_fn res) state_fn"

||| `Bind` is always defined the same way, but requires the name of the DSA to
||| make sense (because the name is part of the name of the `Cmd` type)
dsa2Bind : DSA2 -> String
dsa2Bind (MkDSA2 dsaName  _ _ _) =
  let cmdName = dsaName ++ "Cmd"
  in indent
     ++ "(>>=) :  " ++ cmdName  ++ " a state1 state2_fn" ++ "\n" ++ indent
     ++ "      -> ((res : a) -> " ++ cmdName ++ " b (state2_fn res) state3_fn)" ++ "\n" ++ indent
     ++ "      -> " ++ cmdName ++ " b state1 state3_fn"

||| Naïvely generate Idris source by magically outputting the right string.
||| /!\ EXTREMELY FRAGILE /!\
export
unsafeGenIdris2 : DSA2 -> String
unsafeGenIdris2 dsa@(MkDSA2 dsaName states regEdges depEdges) =
  let statesStr  = genStates states
      depResData = genDepResData depEdges
      cmdDecln   = genCmdHeader
      regCmds    = genRegCmds regEdges
      depCmds    = genDepCmds depEdges
      pureCmd    = dsa2Pure dsa
      bindCmd    = dsa2Bind dsa
  in lineSeparate [ "-- /!\\ UNSAFELY GENERATED /!\\ -- "
                  , statesStr
                  , depResData
                  , cmdDecln
                  , regCmds
                  , depCmds
                  , pureCmd
                  , bindCmd
                  ]
  where
    ||| Line-separate the given list of strings, i.e. insert two newlines
    ||| between each String.
    lineSeparate : List String -> String
    lineSeparate xs = join "\n\n" xs

    ||| States are a datatype named based on the name of the DSA (e.g. if the
    ||| DSA is named "ATM", the datatype becomes "ATMState") where the
    ||| constructors are the names of the states.
    genStates : List State -> String
    genStates xs =
      "data " ++ dsaName ++ "State = " ++ (join " | " $ map show states)

    ||| Regular commands have a name corresponding the the `RegEdge`'s name,
    ||| their command-name depends on the name of the DSA, they do nothing, so
    ||| they return `Unit`, and they always go to the same destination, i.e.
    ||| "const <to>".
    genRegCmds : List RegEdge -> String
    genRegCmds [] = ""
    genRegCmds ((MkRegEdge reName from to) :: res) =
      indent
      ++ show reName ++ " : " ++ dsaName ++ "Cmd () " ++ show from ++ " (const " ++ show to ++ ")"
      ++ "\n" ++ genRegCmds res

    ||| For each of the `DepRes`'s of the `DepEdge`s to work, there needs to be
    ||| a datatype whose name is (`DepRes`.name ++ "Res") and whose constructors
    ||| are the result names of each of the `DepRes`'s of the edge.
    genDepResData : List DepEdge -> String
    genDepResData [] = ""
    genDepResData ((MkDepEdge name _ depTo) :: des) =
      let dataName = show name ++ "Res"
          depResNames = map getResName depTo
      in "data " ++ dataName ++ " = " ++ (join " | " depResNames)

    ||| Every `DepRes` is just a part of a `case` stmt from its `resName` to its
    ||| `to` part, e.g.
    ||| `(MkDepRes PIN_OK Session)` --> `PIN_OK => Session`
    genDepResCases : List DepRes -> List String
    genDepResCases [] = []
    genDepResCases ((MkDepRes resName to) :: drs) =
      (resName ++ " => " ++ show to) :: genDepResCases drs

    ||| Dependent commands have a name corresponding to the `DepEdge`'s name,
    ||| their command-name depends on the name of DSA, and they have a single
    ||| starting point/"from", same as a `RegEdge`, **BUT** they return a
    ||| result (based on their name ++ "Res"), and their "to" part is a `case`
    ||| function whose cases are each of the `DepRes`s in the edge's `depTo`
    ||| field.
    genDepCmds : List DepEdge -> String
    genDepCmds [] = ""
    genDepCmds ((MkDepEdge deName from depTo) :: des) =
      let cmdName = dsaName ++ "Cmd"
          resName = show deName ++ "Res"
          cases   = genDepResCases depTo
      in indent
         ++ show deName ++ " : " ++ cmdName ++ " " ++ resName ++ " " ++ show from
         ++ " (\\depRes => case depRes of " ++ (join "; " cases) ++ ")"
         ++ "\n" ++ genDepCmds des

    ||| The command datatype's declaration depends on the name of the DSA.
    genCmdHeader : String
    genCmdHeader =
      let cmdName   = dsaName ++ "Cmd"
          stateName = dsaName ++ "State"
      in "data " ++ cmdName ++ " : (ty : Type) "
         ++ " -> " ++ stateName
         ++ " -> " ++ "(ty -> " ++ stateName ++ ")"
         ++ " -> Type where"

--- ||| Naïvely generate Idris source by magically outputting the right string.
--- ||| EXTREMELY FRAGILE!
--- export
--- unsafeGenIdris : DSA -> String
--- unsafeGenIdris (MkDSA states edges) =
---   let
---     -- first: create a data-type containing every state
---     statesStr = genStates states
---     -- then, separate the regular from the dependent actions
---     (regs, deps) = sortEdges edges
---     -- second: create a data-type for each of the dependent results, with
---     --         constructors for each alternative
---     depResStr = lineSeparate $ handleDepStates deps
---     -- third: define `Cmd` data-type containing all the transitions as
---     -- constructors
---     cmdDataStr = genCmds regs deps
---   in
---     lineSeparate ["-- UNSAFELY GENERATED! --"
---                  , statesStr
---                  , depResStr
---                  , cmdDataStr
---                  , dsaPure
---                  , dsaBind
---                  ]
---   where
---     -- Data.String.Extra.join
---     lineSeparate : List String -> String
---     lineSeparate xs = join "\n\n" xs
--- 
---     -- generate a `State` data-type whose constructors are each of the possible
---     -- states in the DSA
---     genStates : List State -> String
---     genStates states =
---       "data State = " ++ (join " | " $ map show states)
--- 
---     -- generate a data-type for each DepAction's result type, containing
---     -- constructors for each of the 
---     handleDepStates : List Edge -> List String
---     handleDepStates [] = []
---     handleDepStates ((RegAction _ _ _) :: es) =
---       assert_total $ idris_crash "Got a RegAction in handleDepStates."
---     handleDepStates ((DepAction l from depTo) :: es) =
---       ("data " ++ show l ++ "Res = " ++ (join " | " $ map getResName depTo))
---       :: handleDepStates es
--- 
---     -- regular commands have a name, and always use `const <to>` as their
---     -- `state_fn`
---     genRegCmds : List Edge -> String
---     genRegCmds [] = ""
---     genRegCmds ((RegAction l from to) :: es) =
---       indent
---       ++ show l ++ " : Cmd () " ++ show from ++ " (const " ++ show to ++ ")"
---       ++ "\n" ++ genRegCmds es
---     genRegCmds ((DepAction _ _ _) :: es) =
---       assert_total $ idris_crash "Got a DepAction in genRegCmds."
--- 
---     -- cases in a dependent state function have the form
---     -- <ResName> => <destState>
---     genDepStateCases : List DepRes -> List String
---     genDepStateCases [] = []
---     genDepStateCases ((MkDepRes resName to) :: es) =
---       (resName ++ " => " ++ show to) :: genDepStateCases es
--- 
---     -- dependent commands occur **exactly once** per labelled transition, the
---     -- changing step is that their `state_fn` is an anonymous function to
---     -- various states
---     genDepCmds : List Edge -> String
---     genDepCmds [] = ""
---     genDepCmds ((RegAction _ _ _) :: es) =
---       assert_total $ idris_crash "Got a RegAction in genDepCmds"
---     genDepCmds ((DepAction l from depTo) :: es) =
---       indent
---       ++ show l ++ " : Cmd " ++ show l ++ "Res " ++ show from
---       ++ " (\\depRes => case depRes of " ++ (join "; " $ genDepStateCases depTo)
---       ++ ")\n" ++ genDepCmds es
--- 
---     -- generate the `Cmd` data-type, by generating the regular commands first,
---     -- followed by the dependent commands
---     genCmds : (regs : List Edge) -> (deps : List Edge) -> String
---     genCmds regs deps =
---       "data Cmd : (ty : Type) -> State -> (ty -> State) -> Type where"
---       ++ "\n"
---       ++ genRegCmds regs
---       ++ genDepCmds deps

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

s1s2 : RegEdge
s1s2 = MkRegEdge (MkLabel "InsertCard") atm_s1 atm_s2

s2s2 : RegEdge
s2s2 = MkRegEdge (MkLabel "GetPIN") atm_s2 atm_s2

s2dep : DepEdge
s2dep = MkDepEdge (MkLabel "CheckPin")
                  atm_s2
                  [MkDepRes "Incorrect" atm_s2, MkDepRes "Correct" atm_s3]

s3s3 : RegEdge
s3s3 = MkRegEdge (MkLabel "Dispense") atm_s3 atm_s3

-- NOT QUITE CORRECT:
anyS1 : RegEdge
anyS1 = MkRegEdge (MkLabel "EjectCard") any atm_s1

-- s2s1 : Edge
-- s2s1 = RegAction (MkLabel "EjectCard") atm_s2 atm_s1
-- 
-- s3s1 : Edge
-- s3s1 = RegAction (MkLabel "EjectCard") atm_s3 atm_s1

export
atm : DSA2
atm = MkDSA2 "ATM"
             [atm_s1, atm_s2, atm_s3]
             [s1s2, s2s2, s3s3, anyS1]
             [s2dep]

