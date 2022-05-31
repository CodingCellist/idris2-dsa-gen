module DSAGen.Idris2CodeGen

import DSAGen.DSLv2
import DSAGen.Parser

import Data.DPair
import Data.String

%default total

------------------------
-- Static definitions --
------------------------

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
genDataCons : (dcTy : String) -> Subset Value IsDataVal -> String
genDataCons dcTy (Element (DataVal dc Nothing) isDV) = "\{dc} : \{dcTy}"
genDataCons dcTy (Element (DataVal dc (Just args)) isDV) =
  let argStrings = map genValue args
      argString = joinBy " -> " $ toList argStrings
  in "\{dc} : \{argString} -> \{dcTy}"

----------------
-- Command CG --
----------------

--- ||| A plain command is a constructor which takes no arguments and goes to a
--- ||| constant state.
--- genPlainCmd : (dsaName : String) -> Subset DSALabel IsPlainCmd -> String
--- genPlainCmd dsaName (Element (PlainCmd cmd) isPlain) =
---   "\{cmd} : \{dsaName}Cmd () ?genPlainCmd_rhs_1"

-----------------------
-- Universal Edge CG --
-----------------------

||| A universal edge can be taken from anywhere in the DSA, and so does not name
||| a specific state in its command definition.
genUniversalEdge : (dsaName : String) -> (ue : UniversalEdge) -> String
genUniversalEdge dsaName (MkUniversalEdge
                         (Element (PlainCmd cmd) isPlain)
                         (Element (DataVal to args) isDV)
                         ) =
  -- TODO: Resume here, but it's going to be a bit complicated...
  ?genUniversalEdge_rhs -- "\{cmd} : \{dsaName}Cmd () anyState (const \{to})"

-----------------------
-- Generating Idris2 --
-----------------------

||| Convert the given `DSA` to Idris2 source code.
export
toIdris2 : DSAv2 -> String
toIdris2 (MkDSAv2 dsaName states edges universalEdges) = ?toIdris_rhs_0


--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------

||| "Test : ATMCmd"
covering
testGenDataCons1 : String
testGenDataCons1 =
  genDataCons "ATMCmd" (Element (DataVal "Test" Nothing) ItIsDataVal)

||| "Test : sn -> ATMCmd"
covering
testGenDataCons2 : String
testGenDataCons2 =
  genDataCons "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: []))) ItIsDataVal)

||| "Test : sn -> (sn + 1) -> ATMCmd"
covering
testGenDataCons3 : String
testGenDataCons3 =
  genDataCons "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: [AddExpr (IdrName "sn") (LitVal 1)]))) ItIsDataVal)

