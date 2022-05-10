module DSAGen.DSLv2

import DSAGen.Parser

import Data.List
import Data.List1
import Data.String
import Data.List.Quantifiers

||| A proof that the `Value` is a data constructor value.
public export
data IsDataVal : Value -> Type where
  ItIsDataVal : IsDataVal (DataVal _ _)

||| A proof that the `DSALabel` is a plain command (i.e. takes no arguments).
public export
data IsPlainCmd : DSALabel -> Type where
  ItIsPlain : IsPlainCmd (PlainCmd _)

||| A Dependent State Automata is a collection of:
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

