module DSAGen.Idris2CodeGen

import DSAGen.DSLv2
import DSAGen.Parser

import Data.DPair
import Data.String

%default total

------------------------
-- Static definitions --
------------------------

||| No result is defined as Unit.
noRes : String
noRes = "()"

||| Pure is always defined for DSAs in the same way.
pure : (dsaName : String) -> String
pure dsaName =
  "Pure : (res : resTy) -> \{dsaName}Cmd resTy (state_fn res) state_fn"

||| Bind (>>=) is always defined for DSAs in the same way.
bind : (dsaName : String) -> String
bind dsaName =
  "(>>=) :  \{dsaName}Cmd resTy state_1 state2_fn\n" ++
  "      -> (contn : (res : resTy) -> \{dsaName}Cmd cResTy (state2_fn res) state3_fn)\n" ++
  "      -> \{dsaName}Cmd cResTy state_1 state3_fn"


------------------------
-- Type-gen functions --
------------------------

||| The data type for DSA states is based on the DSA's name.
stateType : (dsaName : String) -> String
stateType dsaName =
  "data \{dsaName}State : Type where"

||| The data type for DSA commands is based on the DSA's name and carries the
||| result type, the current state, and a function from the result type to the
||| next state.
cmdType : (dsaName : String) -> String
cmdType dsaName =
  "data \{dsaName}Cmd : (resTy : Type) -> \{dsaName}State -> (resTy -> \{dsaName}State) -> Type where"


||| The barebones command type string
commandTy : (dsaName : String) -> String
commandTy dsaName = "\{dsaName}Cmd"

||| The barebones state type string
stateTy : (dsaName : String) -> String
stateTy dsaName = "\{dsaName}State"


----------------
-- DataVal CG --
----------------

||| /!\ USE AS PART OF FUNCTIONS ONLY /!\
|||
||| A value is one of:
|||   - an Idris name
|||   - an integer literal
|||   - a data constructor, optionally taking some values as arguments
|||   - the addition of two values
|||   - a tuple of values
covering
genValue : Value -> String
-- ez
genValue (IdrName n) = n
genValue (LitVal lit) = show lit
genValue (DataVal dc Nothing) = "(\{dc})"
-- funky
genValue (DataVal dc (Just args)) =
  let argString = joinBy " " (genValue <$> toList args)
  in "(\{dc} \{argString})"

genValue (AddExpr num addend) =
  let numStr = genValue num
      addendStr = genValue addend
  in "(\{numStr} + \{addendStr})"

genValue (Tuple fst snd) = "(\{genValue fst}, \{genValue snd})"

||| A data value is a data constructor, optionally taking some arguments.
|||
||| @ dcTy a string representing the return type of the data constructor
covering
genDataConsDecl : (dcTy : String) -> Subset Value IsDataVal -> String
genDataConsDecl dcTy (Element (DataVal dc Nothing) isDV) = "\{dc} : \{dcTy}"
genDataConsDecl dcTy (Element (DataVal dc (Just args)) isDV) =
  let argStrings = map genValue args
      argString = joinBy " -> " $ toList argStrings
  in "\{dc} : \{argString} -> \{dcTy}"

-------------
-- Edge CG --
-------------

||| A plain command is a constructor which takes no arguments and always goes to
||| the same state (i.e. no dependent transition).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the plain command.
covering
genPlainEdge : (dsaName : String) -> (edge : Subset DSAEdge IsPlainEdge) -> String
genPlainEdge dsaName (Element (MkDSAEdge (PlainCmd cmd) from to) isPlain) =
  let cmdStart = commandTy dsaName
      fromState = genValue from.fst
      toState = genValue to.fst
  in "\{cmd} : \{cmdStart} \{noRes} \{fromState} (const \{toState})"

-----------------------
-- Universal Edge CG --
-----------------------

||| A universal edge can be taken from anywhere in the DSA, and so does not name
||| a specific state in its command definition.
covering
genUniversalEdge : (dsaName : String) -> (ue : UniversalEdge) -> String
genUniversalEdge dsaName (MkUniversalEdge
                         (Element (PlainCmd cmd) isPlain)
                         (Element dest@(DataVal to args) isDV)
                         ) =
  let cmdStart = commandTy dsaName
      destState = genValue dest
  in "\{cmd} : \{cmdStart} \{noRes} anyState (const \{destState})"

-----------------------
-- Generating Idris2 --
-----------------------

||| Convert the given `DSA` to Idris2 source code.
export
toIdris2 : DSAv2 -> String
toIdris2 (MkDSAv2 dsaName states edges universalEdges) =
  let states = ?genStates dsaName states
      edges = ?genEdges dsaName edges
      ues = map (genUniversalEdge dsaName) universalEdges
  in ?toIdris_rhs_0


--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------

-------------------------
-- Basic data cons gen --
-------------------------

||| "Test : ATMCmd"
covering
testGenDataCons1 : String
testGenDataCons1 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" Nothing) ItIsDataVal)

||| "Test : sn -> ATMCmd"
covering
testGenDataCons2 : String
testGenDataCons2 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: []))) ItIsDataVal)

||| "Test : sn -> (sn + 1) -> ATMCmd"
covering
testGenDataCons3 : String
testGenDataCons3 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: [AddExpr (IdrName "sn") (LitVal 1)]))) ItIsDataVal)


------------
-- UE gen --
------------

||| "UETest : ATMCmd () anyState (const Ready)"
covering
testGenUE1 : String
testGenUE1 =
  let cmd : Subset DSALabel IsPlainCmd
          = Element (PlainCmd "UETest") ItIsPlain
      dest : Subset Value IsDataVal
           = Element (DataVal "Ready" Nothing) ItIsDataVal
  in genUniversalEdge "ATM" (MkUniversalEdge cmd dest)

||| "UETest : ATMCmd () anyState (const (Ready a b))"
covering
testGenUE2 : String
testGenUE2 =
  let cmd : Subset DSALabel IsPlainCmd
          = Element (PlainCmd "UETest") ItIsPlain
      dest : Subset Value IsDataVal
           = Element (DataVal "Ready" (Just $ (IdrName "a") ::: [IdrName "b"])) ItIsDataVal
  in genUniversalEdge "ATM" (MkUniversalEdge cmd dest)

--------------------
-- Plain edge gen --
--------------------

||| "EjectCard : ATMCmd () Session (const Ready)
covering
testGenPlainEdge1 : String
testGenPlainEdge1 =
  genPlainEdge "ATM" edge
  where
      cmd : DSALabel
      cmd = PlainCmd "EjectCard"

      from : Subset Value IsDataVal
      from = Element (DataVal "Session" Nothing) ItIsDataVal

      to : Subset Value IsDataVal
      to = Element (DataVal "Ready" Nothing) ItIsDataVal

      edge : Subset DSAEdge IsPlainEdge
      edge = Element (MkDSAEdge cmd from to) EdgeIsPlain

||| "EjectCard : ATMCmd () (Session (c, d)) (const (Ready a (b + 2)))
covering
testGenPlainEdge2 : String
testGenPlainEdge2 =
  genPlainEdge "ATM" edge
  where
      cmd : DSALabel
      cmd = PlainCmd "EjectCard"

      fromArgs : Maybe $ List1 Value
      fromArgs = Just $ (Tuple (IdrName "c") (IdrName "d")) ::: []

      from : Subset Value IsDataVal
      from = Element (DataVal "Session" fromArgs) ItIsDataVal

      toArgs : Maybe $ List1 Value
      toArgs = Just $ (IdrName "a") ::: [AddExpr (IdrName "b") (LitVal 2)]

      to : Subset Value IsDataVal
      to = Element (DataVal "Ready" toArgs) ItIsDataVal

      edge : Subset DSAEdge IsPlainEdge
      edge = Element (MkDSAEdge cmd from to) EdgeIsPlain

