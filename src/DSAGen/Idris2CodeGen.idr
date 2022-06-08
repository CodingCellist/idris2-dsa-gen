module DSAGen.Idris2CodeGen

import DSAGen.DSLv2
import DSAGen.Parser

import Data.DPair
import Data.String

%default total

--------------------------------------------------------------------------------
-- HELPERS
--------------------------------------------------------------------------------

------------------------
-- Proofs/Constraints --
------------------------

data IsTakeEdge : DSAEdge -> Type where
  ItIsTakeEdge : IsTakeEdge (MkDSAEdge (TakeCmd _ _) _ _)

data IsDepEdge : DSAEdge -> Type where
  ItIsDepEdge : IsDepEdge (MkDSAEdge (DepCmd _ _) _ _)

data IsProdEdge : DSAEdge -> Type where
  ItIsProdEdge : IsProdEdge (MkDSAEdge (ProdCmd _ _) _ _)

data IsTDEdge : DSAEdge -> Type where
  ItIsTDEdge : IsTDEdge (MkDSAEdge (TDCmd _ _ _) _ _)

data IsTPEdge : DSAEdge -> Type where
  ItIsTPEdge : IsTPEdge (MkDSAEdge (TPCmd _ _ _) _ _)

data IsDPEdge : DSAEdge -> Type where
  ItIsDPEdge : IsDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)

data IsTDPEdge : DSAEdge -> Type where
  ItIsTDPEdge : IsTDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)

----------------
-- Data types --
----------------

||| A dependent result links a case of the edge's dependency value to the
||| corresponding state.
record DepRes where
  constructor MkDepRes
  depCase : DepArg
  caseTo : Subset Value IsDataVal

||| The result of accumulating all the dependent edges of a depedent command.
record DepCmdAcc where
  constructor MkDCAcc
  ||| The name of the command.
  cmd : String

  ||| The state the command starts at.
  from : Subset Value IsDataVal

  ||| The list of value-state pairs that the command can dependently go to.
  cases : List1 DepRes


---------------------------
-- Accumulator functions --
---------------------------

||| Initialise the dependent edge accumulator using the given dependent edge.
initDEAcc :  (iDepEdge : DSAEdge)
          -> {auto 0 constraint : IsDepEdge iDepEdge}
          -> DepCmdAcc
initDEAcc (MkDSAEdge (DepCmd cmd depCase) from to) =
  MkDCAcc cmd from (singleton $ MkDepRes depCase to)

||| Add the dependent edge's case-dest pair to the accumulator.
|||
||| @ acc The dependent edge accumulator.
||| @ depEdge The edge whose case-dest pair to add.
addDECase :  (acc : DepCmdAcc)
          -> (depEdge : DSAEdge)
          -> {auto 0 constraint : IsDepEdge depEdge}
          -> DepCmdAcc
addDECase acc (MkDSAEdge (DepCmd cmd depCase) from to) =
  { cases $= cons (MkDepRes depCase to) } acc


||| Accumulate the list of dependent edges into a single data-structure keeping
||| track of the dependent results.
-- FIXME: need to port+merge Data.List.Quantifiers to Data.List1.Quantifiers
-- accDEs : (des : Subset (List1 DSAEdge) (All IsDepEdge)) -> DepCmdAcc


--------------------------------------------------------------------------------
-- CODE GEN
--------------------------------------------------------------------------------

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

-----------
-- Edges --
-----------

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

||| A command which takes a value is a function from the argument to a
||| constructor which produces nothing and goes to a constant state (or it would
||| be a take-dep command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the take command
covering
genTakeEdge :  (dsaName : String)
            -> (edge : DSAEdge)
            -> {auto 0 constraint : IsTakeEdge edge}
            -> String
genTakeEdge dsaName (MkDSAEdge (TakeCmd cmd (Takes arg)) from to) =
  let cmdTyStart = commandTy dsaName
      argStr = genValue arg
      fromState = genValue from.fst
      toState = genValue to.fst
  in "\{cmd} : \{argStr} -> \{cmdTyStart} \{noRes} \{fromState} (const \{toState})"

||| A command which produces a value is a constructor with the result as the
||| return type, and it must always go to the same state (or it would be a
||| prod-dep command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the prod command
covering
genProdEdge :  (dsaName : String)
            -> (edge : DSAEdge)
            -> {auto 0 constraint : IsProdEdge edge}
            -> String
genProdEdge dsaName (MkDSAEdge (ProdCmd cmd (Produce val)) from to) =
  let cmdTyStart = commandTy dsaName
      resStr = genValue val
      fromState = genValue from.fst
      toState = genValue to.fst
  in "\{cmd} : \{cmdTyStart} \{resStr} \{fromState} (const \{toState})"

||| A command which takes and produces a value is a function from the argument
||| to a constructor with the result as the return type, and it must always go
||| to the same state (or it would be a take-dep-prod command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the take-prod command.
covering
genTPEdge :  (dsaName : String)
          -> (edge : DSAEdge)
          -> {auto 0 constraint : IsTPEdge edge}
          -> String
genTPEdge dsaName (MkDSAEdge (TPCmd cmd (Takes arg) (Produce val)) from to) =
  let cmdTyStart = commandTy dsaName
      argStr = genValue arg
      resStr = genValue val
      fromState = genValue from.fst
      toState = genValue to.fst
  in "\{cmd} : \{argStr} -> \{cmdTyStart} \{resStr} \{fromState} (const \{toState})"

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

-------------------
-- Take-edge gen --
-------------------

||| "CheckPIN : PIN -> ATMCmd () CardInserted (const Session)"
covering
testGenTakeEdge1 : String
testGenTakeEdge1 =
  genTakeEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    arg : TakeArg
    arg = Takes (IdrName "PIN")

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (TakeCmd cmd arg) from to

||| "CheckPIN : (PIN, (1 + n)) -> ATMCmd () (CardInserted (c, d)) (const (Session a (b + 2)))"
covering
testGenTakeEdge2 : String
testGenTakeEdge2 =
  genTakeEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    arg : TakeArg
    arg = Takes (Tuple (IdrName "PIN") (AddExpr (LitVal 1) (IdrName "n")))

    fromArgs : Maybe $ List1 Value
    fromArgs = Just $ (Tuple (IdrName "c") (IdrName "d")) ::: []

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" fromArgs) ItIsDataVal

    toArgs : Maybe $ List1 Value
    toArgs = Just $ (IdrName "a") ::: [AddExpr (IdrName "b") (LitVal 2)]

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" toArgs) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (TakeCmd cmd arg) from to

-------------------
-- Prod-edge gen --
-------------------

||| "CheckPIN : ATMCmd (PINCheck) CardInserted (const Session)"
covering
testGenProdEdge1 : String
testGenProdEdge1 =
  genProdEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    res : ProdArg
    res = Produce (DataVal "PINCheck" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (ProdCmd cmd res) from to

||| "CheckPIN : ATMCmd ((PINCheck pin), sTok) (CardInserted (c, (1 + d))) (const (Session sTok))"
covering
testGenProdEdge2 : String
testGenProdEdge2 =
  genProdEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    pcArg : Maybe $ List1 Value
    pcArg = Just $ (IdrName "pin") ::: []

    res : ProdArg
    res = Produce (Tuple (DataVal "PINCheck" pcArg) (IdrName "sTok"))

    fromArgs : Maybe $ List1 Value
    fromArgs = Just $
               (Tuple (IdrName "c") (AddExpr (LitVal 1) (IdrName "d"))) ::: []

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" fromArgs) ItIsDataVal

    toArgs : Maybe $ List1 Value
    toArgs = Just $ (IdrName "sTok") ::: []

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" toArgs) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (ProdCmd cmd res) from to

------------------------
-- Take-prod-edge gen --
------------------------

||| "CheckPIN : (PIN) -> ATMCmd (PINCheck) (CardInserted) (const (Session))"
covering
testGenTPEdge1 : String
testGenTPEdge1 =
  genTPEdge "ATM" tpEdge
  where
    cmd : String
    cmd = "CheckPIN"

    takes : TakeArg
    takes = Takes (DataVal "PIN" Nothing)

    returns : ProdArg
    returns = Produce (DataVal "PINCheck" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    tpEdge : DSAEdge
    tpEdge = MkDSAEdge (TPCmd cmd takes returns) from to

||| "Send : (SeqNo sn) -> ARQCmd ((SeqNo sn), (csn + 1)) (Ready sn csn) (const (Waiting sn (csn + 1)))"
covering
testGenTPEdge2 : String
testGenTPEdge2 =
  genTPEdge "ARQ" tpEdge
  where
    cmd : String
    cmd = "Send"

    -- sequence number
    sn : Value
    sn = IdrName "sn"

    seqNo : Value
    seqNo = DataVal "SeqNo" (Just (sn ::: []))

    takes : TakeArg
    takes = Takes seqNo

    -- current sequence number
    csn : Value
    csn = IdrName "csn"

    one : Value
    one = LitVal 1

    returns : ProdArg
    returns = Produce (Tuple seqNo (AddExpr csn one))

    from : Subset Value IsDataVal
    from = Element (DataVal "Ready" (Just (sn ::: [csn]))) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Waiting" (Just (sn ::: [AddExpr csn one]))) ItIsDataVal

    tpEdge : DSAEdge
    tpEdge = MkDSAEdge (TPCmd cmd takes returns) from to

