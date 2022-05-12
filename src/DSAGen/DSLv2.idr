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
-- DATA TYPES --
--------------------------------------------------------------------------------

||| A proof that the `Value` is a data constructor value.
public export
data IsDataVal : Value -> Type where
  ItIsDataVal : IsDataVal (DataVal _ _)

||| A proof that the `DSALabel` is a plain command (i.e. takes no arguments).
public export
data IsPlainCmd : DSALabel -> Type where
  ItIsPlain : IsPlainCmd (PlainCmd _)

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

  ||| There was an error when parsing the String as a Value
  ValueParseError :  (concerning : String)
                  -> (parseErrors : List1 (ParsingError LabelTok))
                  -> ToDSAError

  ||| It was not possible to parse the given String completely.
  ValueRemainderError :  (concerning : String)
                      -> (rem : List (WithBounds LabelTok))
                      -> ToDSAError

  ||| The given Stmt cannot be converted to a DSA state
  StmtStateError : (stmt : Stmt) -> ToDSAError

  ||| The given String cannot be converted to an Idris data constructor value
  StringDataValError : (str : String) -> ToDSAError
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
          (val, rem@(_ :: _)) => Left $ ValueRemainderError s rem

||| Convert the given string to a valid Idris data constructor value, if it is
||| one.
stringToIdrisDataVal : String -> Either ToDSAError (Subset Value IsDataVal)
stringToIdrisDataVal s =
  do val <- stringToIdrisValue s
     case val of
          dv@(DataVal dc args) => pure (Element dv ItIsDataVal)
          _ => Left $ StringDataValError s

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
          (Left e@(ValueRemainderError _ _)) => Left e
          (Left _) => Left $ DSANameError dotid
          (Right (DataVal dc Nothing)) => pure dc
          (Right _) => Left $ DSANameError dotid

dotidToDSAName dotid@(NameID nameID) =
  case stringToIdrisValue nameID of
       (Left e@(UnknownLexemeError _ _)) => Left e
       (Left e@(ValueParseError _ _)) => Left e
       (Left e@(ValueRemainderError _ _)) => Left e
       (Left _) => Left $ DSANameError dotid
       (Right (DataVal dc Nothing)) => pure dc
       (Right _) => Left $ DSANameError dotid

dotidToDSAName dotid = Left $ DSANameError dotid

------------
-- States --
------------

||| Convert a DOT `Stmt` to a DSA state.
|||
||| A `Stmt` is a state iff it is:
|||   - a `NodeStmt` without any attributes, containing either a `NameID` or a
|||     `StringID`, whose value is a valid Idris data constructor;
|||   OR
|||   - an `EdgeStmt` not involving a subgraph, TODO...
dotStmtToState : Stmt -> Either ToDSAError (Subset Value IsDataVal)
dotStmtToState (NodeStmt (MkNodeID (NameID name) _) [[]]) =
  stringToIdrisDataVal name
dotStmtToState (NodeStmt (MkNodeID (StringID id_) _) [[]]) =
  stringToIdrisDataVal $ cleanStringIDString id_

dotStmtToState (EdgeStmt (Left nodeID) rhs attrList) = ?dotStmtToState_rhs_5

dotStmtToState stmt = Left $ StmtStateError stmt
-- FIXME: Show Edwin this: dotStmtToState stmt = Left $ ?searchme

||| Convert the DOT `Stmt`s to states in a DSA, accumulating the states in the
||| given accumulator iff the state to add is unique.
covering
dotStmtsToAccStates :  List Stmt
                    -> (acc : List (Subset Value IsDataVal))
                    -> Either ToDSAError (List (Subset Value IsDataVal))
dotStmtsToAccStates [] acc = pure acc
dotStmtsToAccStates (stmt :: stmts) acc =
  do state <- dotStmtToState stmt
     if elem state acc
        then dotStmtsToAccStates stmts acc
        else dotStmtsToAccStates stmts (state :: acc)

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

