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
public export
data DSAEdge : Type where
  MkDSAEdge :  (cmd  : DSALabel)
            -> (from : Subset Value IsDataVal)
            -> (to   : Subset Value IsDataVal)
            -> DSAEdge

||| A proof that an edge contains a plain command (i.e. carries no data).
public export
data IsPlainEdge : DSAEdge -> Type where
  EdgeIsPlain : IsPlainEdge (MkDSAEdge (PlainCmd _) _ _)

Uninhabited (IsPlainEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

Uninhabited (IsPlainEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited EdgeIsPlain impossible

||| Prove that the given edge is a plain edge, or produce a counter-proof for
||| why it cannot be a plain edge.
isItPlainEdge : (edge : DSAEdge) -> Dec (IsPlainEdge edge)
isItPlainEdge (MkDSAEdge (PlainCmd _) _ _)     = Yes EdgeIsPlain
isItPlainEdge (MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
isItPlainEdge (MkDSAEdge (DepCmd _ _) _ _)     = No absurd
isItPlainEdge (MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
isItPlainEdge (MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
isItPlainEdge (MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
isItPlainEdge (MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
isItPlainEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

||| A Universal Edge is an edge which can be taken from any state in a DSA back
||| to a single state. Universal Edges are always plain.
public export
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
          -> {allEdges : List DSAEdge}
          -> (edges : Split IsPlainEdge allEdges)
          -> (universalEdges : List UniversalEdge)
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
Show DSAEdge where
  show (MkDSAEdge cmd from to) =
    "(DSAEdge \{show cmd} (\{show from}-->\{show to}))"

export
covering
Show UniversalEdge where
  show (MkUniversalEdge cmd to) =
    "(UniversalEdge \{show cmd} (_-->\{show to}))"

export
covering
Show DSAv2 where
  show (MkDSAv2 dsaName states edges univEdges) =
    "--- BEGIN DSA DEFINITION ---\n\t"
    ++ "Name: " ++ dsaName ++ "\n\t"
    ++ "States:\n\t\t" ++ vertListShow (states.fst) ++ "\n\t"
    ++ "Plain edges:\n\t\t" ++ vertListShow (edges.ayes) ++ "\n\t"
    ++ "Advanced edges:\n\t\t" ++ vertListShow (edges.naws) ++ "\n"
    ++ "Universal edges:\n\t\t" ++ vertListShow (univEdges) ++ "\n"
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

--------
-- Eq --
--------

export
covering
Eq DSAEdge where
  (==) (MkDSAEdge cmd1 from1 to1) (MkDSAEdge cmd2 from2 to2) =
    cmd1 == cmd2 && from1 == from2 && to1 == to2


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
export
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
export
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
export
getAssignLabelString : Assign -> Either ToDSAError String
getAssignLabelString (MkAssign (StringID "\"label\"") (StringID rhs)) =
  pure $ cleanStringIDString rhs
getAssignLabelString (MkAssign (NameID "label") (StringID rhs)) =
  pure $ cleanStringIDString rhs
getAssignLabelString attr = Left $ AssignLabelError attr

||| Convert the given string to a valid DSA label, if it is one.
export
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

||| Returns `True` iff the `DOTID` was a `NameID` or a `StringID` containing the
||| value 'invis'.
export
isInvis : DOTID -> Bool
isInvis (NameID "invis") = True
isInvis (StringID "\"invis\"") = True
isInvis _ = False

||| Remove any assignment whose right-hand-side satisfies the given predicate.
export
filterAssignRHS : (by : DOTID -> Bool) -> List Assign -> List Assign
filterAssignRHS by [] = []
filterAssignRHS by (a@(MkAssign _ rhs) :: as) =
  if isInvis rhs
     then filterAssignRHS by as
     else a :: filterAssignRHS by as

||| Remove any assignment which assigns to the value "invis".
export
filterInvisAssign : List Assign -> List Assign
filterInvisAssign = filterAssignRHS isInvis

||| Returns `True` iff the given edge connects to the given state. Returns
||| `False` otherwise.
covering
goesTo : (edge : DSAEdge) -> (state : Value) -> Bool
goesTo (MkDSAEdge _ _ to) state = to.fst == state

||| Does the given edge have different origin and destination (`from` and `to`)?
covering
diffFromTo : DSAEdge -> Bool
diffFromTo (MkDSAEdge _ from to) = from /= to

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
|||   - only has a single EdgeRHS
|||   - contains only a single list of attribute assignments, of which the first
|||     must assign 'label' to some valid command(s) (separated by ';' if there
|||     are multiple).
dotStmtToLabel : (stmt : Stmt) -> Either ToDSAError (List DSAEdge)
dotStmtToLabel (EdgeStmt (Left lhsID) (erhs ::: []) [(fstAssign :: _)]) =
  do from <- nodeIDToState lhsID
     to <- edgeRHSToState erhs
     rawLabel <- getAssignLabelString fstAssign
     let rawCmds = trim <$> split (== ';') rawLabel
     cmds <- traverse stringToDSALabel rawCmds
     let edges = map (\cmd => MkDSAEdge cmd from to) $ toList cmds
     pure edges

dotStmtToLabel stmt = Left $ StmtCmdError stmt

||| Convert the given DOT `Stmt`s to command labels in a DSA.
|||
||| See also: `dotStmtToLabel`
dotStmtsToLabels : (stmts : List Stmt) -> Either ToDSAError (List DSAEdge)
dotStmtsToLabels [] = pure []
dotStmtsToLabels stmts =
  do multiCmds <- traverse dotStmtToLabel stmts
     pure $ foldl (++) [] multiCmds

||| Split the given `DSAEdge`s into those containing plain DSA commands (i.e.
||| commands taking, producing, and depending on no arguments) and those
||| containing advanced commands.
|||
||| See also: `IsPlainEdge`, `List.Quantifiers.Split`
splitPlainEdges : (edges : List DSAEdge) -> Split IsPlainEdge (reverse edges)
splitPlainEdges = split isItPlainEdge

||| Universal Edge similarity is defined as:
|||   - a plain edge
|||   - whose command name is the same
|||   - whose origin is different
|||   - whose destination is the same
covering
isUniversalEdgeSimilar :  (cand : DSAEdge)
                       -> {auto 0 candOK : IsPlainEdge cand}
                       -> (other : DSAEdge)
                       -> Bool
isUniversalEdgeSimilar (MkDSAEdge (PlainCmd cmd1) from1 to1) other =
  case other of
       (MkDSAEdge (PlainCmd cmd2) from2 to2) =>
            cmd1 == cmd2 && from1 /= from2 && to1 == to2
       _ => False

||| Promote the given edge to a Universal Edge. Since these can be travelled
||| along from anywhere, this REMOVES the edge's `from` part.
toUniversalEdge : (edge : DSAEdge) -> {auto 0 edgeOK : IsPlainEdge edge} -> UniversalEdge
toUniversalEdge (MkDSAEdge cmd@(PlainCmd _) _ to) =
  MkUniversalEdge (Element cmd ItIsPlain) to

||| Extract the Universal Edges to a separate list, removing them from the given
||| list of all edges in the process, and accumulating the Universal Edges and
||| non-Universal Edges in the given accumulator.
covering
extractUniversalEdgesInto :  (states : Subset (List Value) (All IsDataVal))
                          -> (allEdges : List DSAEdge)
                          -> (acc : (List UniversalEdge, List DSAEdge))
                          -> (List UniversalEdge, List DSAEdge)
extractUniversalEdgesInto _ [] acc = acc

extractUniversalEdgesInto states (cand@(MkDSAEdge (PlainCmd cmd) from to) :: es) (accUEs, accEs) =
  let cands = filter (isUniversalEdgeSimilar cand) es
      nStates = length states.fst
      nCands = length cands + 1   -- remember we matched on the current candidate
  in if nCands == nStates
        then let -- newUE = toUniversalEdge cand
                 newUE = toUniversalEdge (MkDSAEdge (PlainCmd cmd) from to)
                 newTail = es \\ cands   -- remove the candidates from the tail
                 newAcc = (newUE :: accUEs, accEs)
             in extractUniversalEdgesInto states newTail newAcc
        else if nCands == (nStates `minus` 1)      -- might not have a NoOp edge
                &&
                all diffFromTo (cand :: cands)     -- check this ^
                then let newUE = toUniversalEdge (MkDSAEdge (PlainCmd cmd) from to)
                         newTail = es \\ cands
                         newAcc = (newUE :: accUEs, accEs)
                     in extractUniversalEdgesInto states newTail newAcc
                else extractUniversalEdgesInto states es (accUEs, cand :: accEs)

extractUniversalEdgesInto states (e@(MkDSAEdge _ from to) :: es) (accUEs, accEs) =
  extractUniversalEdgesInto states es (accUEs, e :: accEs)

||| Extract the Universal Edges to a separate list, removing them from the given
||| list of all edges in the process.
|||
||| See also: `extractUniversalEdgesInto`
covering
extractUniversalEdges :  (states : Subset (List Value) (All IsDataVal))
                      -> (allEdges : List DSAEdge)
                      -> (List UniversalEdge, List DSAEdge)
extractUniversalEdges states allEdges = extractUniversalEdgesInto states allEdges ([], [])

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
     allEdges <- dotStmtsToLabels stmtList
     let (univEdges, dsaEdges) = extractUniversalEdges states allEdges
     let edges = splitPlainEdges dsaEdges
     let dsa = MkDSAv2 dsaName states edges univEdges
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
  in MkDSAv2 dsaName (pullOut listStates) {allEdges=[]} (MkSplit [] []) []

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

