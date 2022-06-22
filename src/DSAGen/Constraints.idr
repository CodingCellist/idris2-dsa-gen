||| Various proof-datatypes and functions for constraining the types found in
||| the DSL and the various parsers.
module DSAGen.Constraints

import DSAGen.DSLv2
import DSAGen.Parser.Value
import DSAGen.Parser.Label

import Data.DPair

--------------------------------------------------------------------------------
-- CONSTRAINTS
--------------------------------------------------------------------------------

--------------------
-- Take-edge only --
--------------------

public export
data IsTakeEdge : DSAEdge -> Type where
  ItIsTakeEdge : IsTakeEdge (MkDSAEdge (TakeCmd _ _) _ _)

public export
data IsDepEdge : DSAEdge -> Type where
  ItIsDepEdge : IsDepEdge (MkDSAEdge (DepCmd _ _) _ _)

public export
isDepEdge : (e : DSAEdge) -> Dec (IsDepEdge e)

public export
data IsProdEdge : DSAEdge -> Type where
  ItIsProdEdge : IsProdEdge (MkDSAEdge (ProdCmd _ _) _ _)

public export
data IsTDEdge : DSAEdge -> Type where
  ItIsTDEdge : IsTDEdge (MkDSAEdge (TDCmd _ _ _) _ _)

public export
data IsTPEdge : DSAEdge -> Type where
  ItIsTPEdge : IsTPEdge (MkDSAEdge (TPCmd _ _ _) _ _)

public export
data IsDPEdge : DSAEdge -> Type where
  ItIsDPEdge : IsDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)

public export
data IsTDPEdge : DSAEdge -> Type where
  ItIsTDPEdge : IsTDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)

||| A proof that a DSA-edge does not involve a dependent state change, i.e. is
||| one of:
|||   - a ProdCmd
|||   - a TakeCmd
|||   - a TPCmd (take-prod)
public export
data IsNonDepEdge : DSAEdge -> Type where
  ItIsProd : IsNonDepEdge (MkDSAEdge (ProdCmd _ _) _ _)
  ItIsTake : IsNonDepEdge (MkDSAEdge (TakeCmd _ _) _ _)
  ItIsTP   : IsNonDepEdge (MkDSAEdge (TPCmd _ _ _) _ _)

||| A `DepCmd` IS a DepEdge
public export
Uninhabited (IsNonDepEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsProd impossible
  uninhabited ItIsTake impossible
  uninhabited ItIsTP impossible

||| A `TDCmd` (take-dep) IS a DepEdge
public export
Uninhabited (IsNonDepEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsProd impossible
  uninhabited ItIsTake impossible
  uninhabited ItIsTP impossible

||| A `DPCmd` (dep-prod) IS a DepEdge
public export
Uninhabited (IsNonDepEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsProd impossible
  uninhabited ItIsTake impossible
  uninhabited ItIsTP impossible

||| A `TDPCmd` (take-dep-prod) IS a DepEdge
public export
Uninhabited (IsNonDepEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsProd impossible
  uninhabited ItIsTake impossible
  uninhabited ItIsTP impossible

||| Prove that the given edge is not a dependent edge, or produce the
||| counter-proof for why it must be a dependent edge.
public export
isItNonDepEdge : (e : DSAEdge) -> Dec (IsNonDepEdge e)
-- TODO: RESUME HERE!!! Caution: Need to exclude plain edges!

