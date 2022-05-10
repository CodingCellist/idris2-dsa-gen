module DSAGen.DSLv2

import DSAGen.Lexer
import DSAGen.Parser
import Graphics.DOT

import Data.List
import Data.List1
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

||| A Dependent State Automaton is a collection of:
|||   - states         -- a list of `Value`s which must be data constructors
|||   - regular edges  -- a list of `DSALabel`s which must be commands taking no
|||                       arguments
|||   - advanced edges -- a list of `DSALabel`s which must be more advanced than
|||                       the regular edges
public export
data DSAv2 : Type where
  MkDSAv2 :  (states : List Value)
          -> {auto 0 statesOK : All IsDataVal states}
          -> (regEdges : List DSALabel)
          -> {auto 0 regsOK : All IsPlainCmd regEdges}
          -> (advEdges : List DSALabel)
          -> {auto 0 advsOK : All (Not . IsPlainCmd) advEdges}
          -> DSAv2

test : DSAv2
test =
  MkDSAv2 [(DataVal "S1" Nothing), (DataVal "S2" Nothing)] [] []


--------------------------------------------------------------------------------
-- READING DOT --
--------------------------------------------------------------------------------

||| The kind of errors that can occur when turning a DOT graph into a DSA.
public export
data ToDSAError : Type where
  ||| The graph was not a graph that can be converted.
  GraphStructureErr : (g : Graph) -> ToDSAError
  -- TODO: the other errors

||| Convert the given DOT `Graph` to a `DSAv2`, reporting what went wrong if
||| anything did.
export
toDSAv2 : Graph -> Either ToDSAError DSAv2
toDSAv2 (MkGraph Nothing DigraphKW (Just id_) stmtList) =
  ?toDSAv2_rhs_7    -- TODO: !!! RESUME HERE !!!
toDSAv2 (MkGraph _ _ _ stmtList) = ?toDSAv2_rhs_2

