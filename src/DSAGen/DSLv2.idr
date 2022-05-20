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

||| Prove that the given command is a plain command, or provide the
||| counter-proof for why it cannot be.
isItPlainCmd : (cmd : DSALabel) -> Dec (IsPlainCmd cmd)
isItPlainCmd (PlainCmd _)     = Yes ItIsPlain
isItPlainCmd (TakeCmd _ _)    = No absurd
isItPlainCmd (DepCmd _ _)     = No absurd
isItPlainCmd (ProdCmd _ _)    = No absurd
isItPlainCmd (TDCmd _ _ _)    = No absurd
isItPlainCmd (TPCmd _ _ _)    = No absurd
isItPlainCmd (DPCmd _ _ _)    = No absurd
isItPlainCmd (TDPCmd _ _ _ _) = No absurd

---------------
-- DSA Edges --
---------------

||| An edge in a Dependent State Automata, connecting two states by a command.
data DSAEdge : Type where
  MkDSAEdge :  (cmd  : DSALabel)
            -> (from : Subset Value IsDataVal)
            -> (to   : Subset Value IsDataVal)
            -> DSAEdge

||| A proof that an edge contains a plain command (i.e. carries no data).
data IsPlainEdge : DSAEdge -> Type where
  ItIsPlainEdge : IsPlainEdge (MkDSAEdge (PlainCmd _) _ _)

||| A Universal Edge is an edge which can be taken from any state in a DSA back
||| to a single state. Universal Edges are always plain.
data UniversalEdge : Type where
  MkUniversalEdge :  (cmd : Subset DSALabel IsPlainCmd)
                  -> (to  : Subset Value IsDataVal)
                  -> UniversalEdge

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
          -> (states : Subset (List Value) (All IsDataVal))
          -> {labels : List DSALabel}
          -> (edges : Split IsPlainCmd labels)
          -> DSAv2

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

  ||| The given NodeID cannot be converted to a DSA state.
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

  ||| The given EdgeRHS cannot be converted to a DSA state.
  EdgeRHSStateError : (erhs : EdgeRHS) -> ToDSAError

  ||| The given Stmt cannot be converted to a DSA command.
  StmtCmdError : (stmt : Stmt) -> ToDSAError


--------------------------------------------------------------------------------
-- INTERFACES
--------------------------------------------------------------------------------

----------
-- Show --
----------

export
covering
Show DSAv2 where
  show (MkDSAv2 dsaName states edges) =
    "--- BEGIN DSA DEFINITION ---\n\t"
    ++ "Name: " ++ dsaName ++ "\n\t"
    ++ "States:\n\t\t" ++ vertListShow (states.fst) ++ "\n\t"
    ++ "Plain edges:\n\t\t" ++ vertListShow (edges.ayes) ++ "\n\t"
    ++ "Advanced edges:\n\t\t" ++ vertListShow (edges.naws) ++ "\n"
    ++ "--- END DSA DEFINITION ---"
    where
      vertListShow : Show a => List a -> String
      vertListShow xs = "[ " ++ joinBy "\n\t\t, " (map show xs) ++ "\n\t\t]"

export
covering
Show ToDSAError where
  show (GraphStructureError g) =
    "The given Graph cannot be converted to a DSA:\n\t" ++ show g

  show (DSANameError id_) =
    "The given DOTID was not a valid DSA name:\n\t" ++ show id_

  show (IdrisNameError id_) =
    "The given DOTID was not a valid Idris name:\n\t" ++ show id_

  show (UnknownLexemeError toLex rem) =
    "It was not possible to lex the given String completely.\n\t"
    ++ "Given: " ++ toLex ++ "\n\t"
    ++ "Remainder: " ++ show rem

  show (ValueParseError concerning parseErrors) =
    "There was an error when parsing the String as a Value.\n\t"
    ++ "Given: " ++ concerning ++ "\n\t"
    ++ "Errors: " ++ show parseErrors

  show (ParseRemainderError concerning rem) =
    "It was not possible to parse the given String completely.\n\t"
    ++ "Given: " ++ concerning ++ "\n\t"
    ++ "Remainder: " ++ show rem

  show (NodeIDStateError nid) =
    "The given NodeID cannot be converted to a DSA state:\n\t" ++ show nid

  show (StmtStateError stmt) =
    "The given Stmt cannot be converted to a DSA state:\n\t" ++ show stmt

  show (StringDataValError str) =
    "The given String cannot be converted to an Idris data constructor value:\n\t"
    ++ str

  show (AssignLabelError attr) =
   "The given assignment was not an assignment from 'label':\n\t" ++ show attr

  show (DSALabelParseError concerning parseErrors) =
    "There was an error when parsing the String as a DSALabel.\n\t"
    ++ "Given: " ++ concerning ++ "\n\t"
    ++ "Errors: " ++ show parseErrors

  show (EdgeRHSStateError erhs) =
    "The given EdgeRHS cannot be converted to a DSA state:\n\t" ++ show erhs

  show (StmtCmdError stmt) =
    "The given Stmt cannot be converted to a DSA command:\n\t" ++ show stmt


--------------------------------------------------------------------------------
-- CONVERTING DOT TO DSAS --
--------------------------------------------------------------------------------

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
||| `NameID`) to a `StringID` rhs. Also cleans the rhs (i.e. removes the
||| surrounding '"') before returning it. Helper-function for `dotStmtToState`.
getAssignLabelString : Assign -> Either ToDSAError String
getAssignLabelString (MkAssign (StringID "\"label\"") (StringID rhs)) =
  pure $ cleanStringIDString rhs
getAssignLabelString (MkAssign (NameID "label") (StringID rhs)) =
  pure $ cleanStringIDString rhs
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

||| Accumulate the new state in the accumulator iff the state is not already an
||| element of the accumulator.
covering
accState :  (newState : Subset Value IsDataVal)
         -> (acc : List (Subset Value IsDataVal))
         -> List (Subset Value IsDataVal)
accState newState acc = if elem newState acc
                           then acc
                           else (newState :: acc)

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
||| An `EdgeStmt` is a state iff it is an `EdgeStmt` not involving a subgraph
||| (in either the LHS or the RHS), having only a single RHS and a single list
||| of assignments of which the first must be a 'label' assignment.
covering
dotStmtsToAccStates :  List Stmt
                    -> (acc : List (Subset Value IsDataVal))
                    -> Either ToDSAError (List (Subset Value IsDataVal))
dotStmtsToAccStates [] acc = pure acc
dotStmtsToAccStates (stmt@(NodeStmt nid [[]]) :: stmts) acc =
  do state <- nodeStmtToState stmt
     dotStmtsToAccStates stmts (accState state acc)

dotStmtsToAccStates ((EdgeStmt (Left lhsID) (eRHS ::: []) [(attr :: _)]) :: stmts) acc =
  do _ <- getAssignLabelString attr   -- check that the RHS is well-formed
     lhsState <- nodeIDToState lhsID
     rhsState <- edgeRHSToState eRHS
     if lhsState == rhsState
        --   if the states are the same, we only need to accumulate one copy
        then dotStmtsToAccStates stmts (accState lhsState acc)
        --   otherwise, we need to accumulate both states
        else dotStmtsToAccStates stmts (accState rhsState (accState lhsState acc))

dotStmtsToAccStates (stmt :: _) acc = Left $ StmtStateError stmt

||| Convert the DOT `Stmt`s to states in a DSA.
covering
dotStmtsToStates :  (stmts : List Stmt)
                 -> Either ToDSAError (Subset (List Value) (All IsDataVal))
dotStmtsToStates stmts = do states <- dotStmtsToAccStates stmts []
                            pure $ pullOut states

-----------
-- Edges --
-----------

||| Convert the given DOT `Stmt` to a command label in a DSA.
|||
||| A `Stmt`'s label is a command iff it:
|||   - does not involve a subgraph (on either the LHS or the RHS)
|||   - contains only a single list of attribute assignments, of which the first
|||     must assign 'label' to some valid command(s) (separated by ';' if there
|||     are multiple).
dotStmtToLabel : (stmt : Stmt) -> Either ToDSAError (List DSALabel)
dotStmtToLabel (EdgeStmt (Left lhsID) rhs [(fstAssign :: _)]) =
  do rawLabel <- getAssignLabelString fstAssign
     let rawCmds = trim <$> split (== ';') rawLabel
     cmds <- traverse stringToDSALabel rawCmds
     pure $ toList cmds

dotStmtToLabel stmt = Left $ StmtCmdError stmt

||| Convert the given DOT `Stmt`s to command labels in a DSA.
|||
||| See also: `dotStmtToLabel`
dotStmtsToLabels : (stmts : List Stmt) -> Either ToDSAError (List DSALabel)
dotStmtsToLabels [] = pure []
dotStmtsToLabels stmts =
  do multiCmds <- traverse dotStmtToLabel stmts
     pure $ foldl (++) [] multiCmds

||| Split the given `DSALabel`s into those containing plain DSA commands (i.e.
||| commands taking, producing, and depending on no arguments) and those
||| containing advanced commands.
|||
||| See also: `IsPlainCmd`, `List.Quantifiers.Split`
labelsToEdges : (labels : List DSALabel) -> Split IsPlainCmd (reverse labels)
labelsToEdges = split isItPlainCmd

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
     labels <- dotStmtsToLabels stmtList
     let edges = labelsToEdges labels
     let dsa = MkDSAv2 dsaName states edges
     pure dsa

toDSAv2 graph = Left $ GraphStructureError graph


--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------

testDSAv2 : DSAv2
testDSAv2 =
  let dsaName : String
              = "Test"
      listStates : List (Subset Value IsDataVal)
                 = [ Element (DataVal "S1" Nothing) ItIsDataVal
                   , Element (DataVal "S2" Nothing) ItIsDataVal]
  in MkDSAv2 dsaName (pullOut listStates) {labels=[]} (MkSplit [] [])

dotFile : String
dotFile =
  "/home/thomas/Documents/01-PhD/idris2-projects/dot-parse/dot-examples/05-ATM-DSAv2.gv"

export
covering
testToDSAv2 : IO ()
testToDSAv2 =
  do Right dot <- readDOTFile dotFile
      | Left err => putStrLn $ "DOT READ ERROR: " ++ show err
     let Right dsa = toDSAv2 dot
          | Left err => putStrLn $ "TODSA ERROR: " ++ show err
     putStrLn "\nSUCCESS!!!\n"
     printLn dsa

