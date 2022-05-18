module DSAGen.DSLv2

import DSAGen.Lexer
import DSAGen.Parser
import Graphics.DOT

import Data.List
import Data.List1
import Data.DPair
import Data.String
import Data.List.Quantifiers

%default total

--------------------------------------------------------------------------------
-- DATA TYPES
--------------------------------------------------------------------------------

------------
-- Proofs --
------------

||| A proof that the `Value` is a data constructor value.
public export
data IsDataVal : Value -> Type where
  ItIsDataVal : IsDataVal (DataVal _ _)

||| A proof that the `DSALabel` is a plain command (i.e. takes no arguments).
public export
data IsPlainCmd : DSALabel -> Type where
  ItIsPlain : IsPlainCmd (PlainCmd _)

-- we need the following `Uninhabited` instances for returning provably
-- non-plain commands

Uninhabited (IsPlainCmd (TakeCmd _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (DepCmd _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (ProdCmd _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (TDCmd _ _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (TPCmd _ _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (DPCmd _ _ _)) where
  uninhabited ItIsPlain impossible

Uninhabited (IsPlainCmd (TDPCmd _ _  _ _)) where
  uninhabited ItIsPlain impossible

------------------------------
-- Dependent State Automata --
------------------------------

||| A Dependent State Automaton has a name, and is a collection of:
|||   - states         -- a list of `Value`s which must be data constructors
|||   - regular edges  -- a list of `DSALabel`s which must be commands taking no
|||                       arguments
|||   - advanced edges -- a list of `DSALabel`s which must be more advanced than
|||                       the regular edges
public export
data DSAv2 : Type where
  MkDSAv2 :  (dsaName : String)
          -> (states : List Value)
          -> {auto 0 statesOK : All IsDataVal states}
          -> (regEdges : List DSALabel)
          -> {auto 0 regsOK : All IsPlainCmd regEdges}
          -> (advEdges : List DSALabel)
          -> {auto 0 advsOK : All (Not . IsPlainCmd) advEdges}
          -> DSAv2

test : DSAv2
test =
  MkDSAv2 "Test" [(DataVal "S1" Nothing), (DataVal "S2" Nothing)] [] []


--------------------------------------------------------------------------------
-- READING DOT --
--------------------------------------------------------------------------------

------------
-- Errors --
------------

||| The kind of errors that can occur when turning a DOT graph into a DSA.
public export
data ToDSAError : Type where
  ||| The graph was not a graph that can be converted.
  GraphStructureError : (g : Graph) -> ToDSAError

  ||| The given DOTID was not a valid DSA name.
  DSANameError : (id_ : DOTID) -> ToDSAError

  ||| The given DOTID was not a valid Idris name.
  IdrisNameError : (id_ : DOTID) -> ToDSAError

  ||| It was not possible to lex the given String completely.
  UnknownLexemeError :  (toLex : String)
                     -> (rem : (Int, Int, String))
                     -> ToDSAError

  ||| There was an error when parsing the String as a Value.
  ValueParseError :  (concerning : String)
                  -> (parseErrors : List1 (ParsingError LabelTok))
                  -> ToDSAError

  ||| It was not possible to parse the given String completely.
  ParseRemainderError :  (concerning : String)
                      -> (rem : List (WithBounds LabelTok))
                      -> ToDSAError

  ||| The given NodeID cannot be converted to a DSA state
  NodeIDStateError : (nid : NodeID) -> ToDSAError

  ||| The given Stmt cannot be converted to a DSA state.
  StmtStateError : (stmt : Stmt) -> ToDSAError

  ||| The given String cannot be converted to an Idris data constructor value.
  StringDataValError : (str : String) -> ToDSAError

  ||| The given assignment was not an assignment from "label".
  AssignLabelError : (attr : Assign) -> ToDSAError

  ||| There was an error when parsing the String as a DSALabel.
  DSALabelParseError :  (concerning : String)
                     -> (parseErrors : List1 (ParsingError LabelTok))
                     -> ToDSAError

  ||| The given String cannot be converted to a plain DSA command.
  StringPlainCommandError : (str : String) -> ToDSAError

  ||| The given String cannot be converted to a non-plain DSA command.
  StringComplexCommandError : (str : String) -> ToDSAError

  ||| The given EdgeRHS cannot be converted to a DSA state
  EdgeRHSStateError : (erhs : EdgeRHS) -> ToDSAError

  -- TODO: the other errors

-----------
-- Utils --
-----------

||| Removes the outer double-quotes (") from a string which was contained in a
||| StringID.
%inline
cleanStringIDString : String -> String
cleanStringIDString id_ = substr 1 ((length id_) `minus` 2) id_

||| Convert the given string to a valid Idris value, if it is one.
stringToIdrisValue : String -> Either ToDSAError Value
stringToIdrisValue s =
  do let (toks, (_, _, "")) = lex s
          | (toks, rem) => Left $ UnknownLexemeError s rem
     let (Right parsed) = parseValue toks
          | Left pErrors => Left $ ValueParseError s pErrors
     case parsed of
          (val, []) => pure val
          (val, rem@(_ :: _)) => Left $ ParseRemainderError s rem

||| Convert the given string to a valid Idris data constructor value, if it is
||| one.
stringToIdrisDataVal : String -> Either ToDSAError (Subset Value IsDataVal)
stringToIdrisDataVal s =
  do val <- stringToIdrisValue s
     case val of
          dv@(DataVal dc args) => pure (Element dv ItIsDataVal)
          _ => Left $ StringDataValError s

||| Extracts the right hand side (rhs) of the assignment, if the given `Assign`
||| is an assignment from the word "label" (either as a `StringID` or a
||| `NameID`) to a `StringID` rhs. Helper-function for `dotStmtToState`.
getAssignLabelString : Assign -> Either ToDSAError String
getAssignLabelString (MkAssign (StringID "\"label\"") (StringID rhs)) = pure rhs
getAssignLabelString (MkAssign (NameID "label") (StringID rhs)) = pure rhs
getAssignLabelString attr = Left $ AssignLabelError attr

||| Convert the given string to a valid DSA label, if it is one.
stringToDSALabel : String -> Either ToDSAError DSALabel
stringToDSALabel s =
  do let (toks, (_, _, "")) = lex s
          | (toks, rem) => Left $ UnknownLexemeError s rem
     let (Right parsed) = parseLabel toks
          | Left pErrors => Left $ DSALabelParseError s pErrors
     case parsed of
          (dsaLabel, []) => pure dsaLabel
          (dsaLabel, rem@(_ :: _)) => Left $ ParseRemainderError s rem

||| Convert the given string to a valid, plain DSA command, if it is one.
|||
||| See also: `IsPlainCmd`.
stringToPlainCmd : String -> Either ToDSAError (Subset DSALabel IsPlainCmd)
stringToPlainCmd s =
  do cmd <- stringToDSALabel s
     case cmd of
          (PlainCmd _) => pure (Element cmd ItIsPlain)
          _ => Left $ StringPlainCommandError s

||| Convert the given string to a valid, non-plain DSA command, if it is one.
|||
||| See also: `IsPlainCmd`
stringToComplexCmd :  String
                   -> Either ToDSAError (Subset DSALabel (Not . IsPlainCmd))
stringToComplexCmd s =
  do cmd <- stringToDSALabel s
     case cmd of
          (PlainCmd _) => Left $ StringComplexCommandError s
          -- need each case separately for proof reasons
          (TakeCmd _ _) => pure (Element cmd uninhabited)
          (DepCmd _ _) => pure (Element cmd uninhabited)
          (ProdCmd _ _) => pure (Element cmd uninhabited)
          (TDCmd _ _ _) => pure (Element cmd uninhabited)
          (TPCmd _ _ _) => pure (Element cmd uninhabited)
          (DPCmd _ _ _) => pure (Element cmd uninhabited)
          (TDPCmd _ _ _ _) => pure (Element cmd uninhabited)

--------------
-- DSA Name --
--------------

||| Check that the given DOTID is a valid name for a DSA, returning the plain
||| string form of the name if it is, and an error if it isn't.
dotidToDSAName : DOTID -> Either ToDSAError String
dotidToDSAName dotid@(StringID id_) =
  let idStr = cleanStringIDString id_   -- StringID includes \"
  in case stringToIdrisValue idStr of
          (Left e@(UnknownLexemeError _ _)) => Left e
          (Left e@(ValueParseError _ _)) => Left e
          (Left e@(ParseRemainderError _ _)) => Left e
          (Left _) => Left $ DSANameError dotid
          (Right (DataVal dc Nothing)) => pure dc
          (Right _) => Left $ DSANameError dotid

dotidToDSAName dotid@(NameID nameID) =
  case stringToIdrisValue nameID of
       (Left e@(UnknownLexemeError _ _)) => Left e
       (Left e@(ValueParseError _ _)) => Left e
       (Left e@(ParseRemainderError _ _)) => Left e
       (Left _) => Left $ DSANameError dotid
       (Right (DataVal dc Nothing)) => pure dc
       (Right _) => Left $ DSANameError dotid

dotidToDSAName dotid = Left $ DSANameError dotid

------------
-- States --
------------

||| Convert a DOT `NodeID` to a DSA state.
|||
||| A `NodeID` is a state iff it contains:
|||   - A `NameID`, whose value is a valid Idris data constructor;
|||   OR
|||   - A `StringID`, whose value is a valid Idris data constructor.
nodeIDToState : NodeID -> Either ToDSAError (Subset Value IsDataVal)
nodeIDToState (MkNodeID (NameID name) _) =
  stringToIdrisDataVal name
nodeIDToState (MkNodeID (StringID id_) _) =
  stringToIdrisDataVal $ cleanStringIDString id_
nodeIDToState nid = Left $ NodeIDStateError nid

||| Convert a DOT `NodeStmt` to a single DSA state.
|||
||| A `NodeStmt` is a state iff it doesn't have any attributes; and it contains
||| either a `NameID` or a `StringID`, whose value is a valid Idris data
||| constructor.
nodeStmtToState : Stmt -> Either ToDSAError (Subset Value IsDataVal)
nodeStmtToState (NodeStmt nid [[]]) = nodeIDToState nid
nodeStmtToState stmt = Left $ StmtStateError stmt

||| Convert a DOT `EdgeRHS` to a DSA state.
|||
||| An `EdgeRHS` is a state iff it is an edge in a digraph (i.e. contains an
||| `Arrow`) pointing to a `DOTID` whose value is a valid Idris data
||| constructor.
covering
edgeRHSToState : EdgeRHS -> Either ToDSAError (Subset Value IsDataVal)
edgeRHSToState (MkEdgeRHS Arrow (Left rhsID)) = nodeIDToState rhsID
edgeRHSToState erhs = Left $ EdgeRHSStateError erhs

||| Convert the DOT `Stmt`s to states in a DSA, accumulating the states in the
||| given accumulator iff the state to add is unique. Only `NodeStmt`s and
||| `EdgeStmt`s can be converted to states. If another kind of statement is
||| present, an error will occur.
|||
||| An `EdgeStmt` is a state iff it is an `EdgeStmt` not involving a subgraph,
||| TODO...
covering
dotStmtsToAccStates :  List Stmt
                    -> (acc : List (Subset Value IsDataVal))
                    -> Either ToDSAError (List (Subset Value IsDataVal))
dotStmtsToAccStates [] acc = pure acc
dotStmtsToAccStates (stmt@(NodeStmt nid [[]]) :: stmts) acc =
  do state <- nodeStmtToState stmt
     if elem state acc
        then dotStmtsToAccStates stmts acc
        else dotStmtsToAccStates stmts (state :: acc)
dotStmtsToAccStates ((EdgeStmt (Left lhsID) (eRHS ::: []) [(attr :: _)]) :: stmts) acc =
  do attrRHS <- getAssignLabelString attr
     _ <- stringToDSALabel attrRHS    -- check that the RHS is well-formed
     state1 <- nodeIDToState lhsID
     state2 <- edgeRHSToState eRHS
     ?helpMeeeeee_1     -- TODO: figure this out
     -- if elem state acc
     --    then dotStmtsToAccStates stmts acc
     --    else dotStmtsToAccStates stmts (state :: acc)

dotStmtsToAccStates (stmt :: _) acc = Left $ StmtStateError stmt

||| Convert the DOT `Stmt`s to states in a DSA.
covering
dotStmtsToStates :  (stmts : List Stmt)
                 -> Either ToDSAError (Subset (List Value) (All IsDataVal))
dotStmtsToStates stmts = do states <- dotStmtsToAccStates stmts []
                            pure $ pullOut states

-----------
-- toDSA --
-----------

||| Convert the given DOT `Graph` to a `DSAv2`, reporting what went wrong if
||| anything did.
export
covering
toDSAv2 : Graph -> Either ToDSAError DSAv2
toDSAv2 (MkGraph Nothing DigraphKW (Just id_) stmtList) =
  do dsaName <- dotidToDSAName id_
     states <- dotStmtsToStates stmtList
     ?toDSAv2_rhs_7    -- TODO: !!! RESUME HERE !!!
toDSAv2 (MkGraph _ _ _ stmtList) = ?toDSAv2_rhs_2

