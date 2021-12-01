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

public export
data DSA : Type where
  MkDSA :  (dsaName  : String)
        -> (states   : List State)
        -> (regEdges : List RegEdge)
        -> (depEdges : List DepEdge)
        -> DSA

||| If `a` describes a Dependent State Automaton, there must be a mapping from
||| `a` to `DSA`.
public export
interface DSADesc a where
  toDSA : a -> DSA


-----------------------------
-- MAGIC STRING GENERATION --
-----------------------------

tabWidth : Nat
tabWidth = 2

indent : String
indent = pack $ replicate tabWidth ' '

||| `Pure` is always defined the same way, but requires the name of the DSA to
||| make sense (because the name is part of the name of the `Cmd` type)
dsaPure : DSA -> String
dsaPure (MkDSA dsaName  _ _ _) =
  indent ++ "Pure : (res : ty) -> " ++ dsaName  ++ "Cmd ty (state_fn res) state_fn"

||| `Bind` is always defined the same way, but requires the name of the DSA to
||| make sense (because the name is part of the name of the `Cmd` type)
dsaBind : DSA -> String
dsaBind (MkDSA dsaName  _ _ _) =
  let cmdName = dsaName ++ "Cmd"
  in indent
     ++ "(>>=) :  " ++ cmdName  ++ " a state1 state2_fn" ++ "\n" ++ indent
     ++ "      -> ((res : a) -> " ++ cmdName ++ " b (state2_fn res) state3_fn)" ++ "\n" ++ indent
     ++ "      -> " ++ cmdName ++ " b state1 state3_fn"

||| Naïvely generate Idris source by magically outputting the right string.
||| /!\ EXTREMELY FRAGILE /!\
export
unsafeGenIdris : DSA -> String
unsafeGenIdris dsa@(MkDSA dsaName states regEdges depEdges) =
  let statesStr  = genStates states
      depResData = genDepResData depEdges
      cmdDecln   = genCmdHeader
      regCmds    = genRegCmds regEdges
      depCmds    = genDepCmds depEdges
      pureCmd    = dsaPure dsa
      bindCmd    = dsaBind dsa
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
atm : DSA
atm = MkDSA "ATM"
            [atm_s1, atm_s2, atm_s3]
            [s1s2, s2s2, s3s3, anyS1]
            [s2dep]

