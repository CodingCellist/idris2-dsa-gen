||| Various proof-datatypes and functions for constraining the types found in
||| the DSL and the various parsers.
module DSAGen.Constraints

import DSAGen.DSLv2
import DSAGen.Parser.Value
import DSAGen.Parser.Label

import Data.DPair

%default total

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
Uninhabited (IsTakeEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible
public export
Uninhabited (IsTakeEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsTakeEdge impossible

-------------------
-- Dep-edge only --
-------------------

public export
data IsDepEdge : DSAEdge -> Type where
  ItIsDepEdge : IsDepEdge (MkDSAEdge (DepCmd _ _) _ _)

public export
Uninhabited (IsDepEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsDepEdge impossible
public export
Uninhabited (IsDepEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsDepEdge impossible

||| Prove that an edge is a dependent edge (i.e. it contains a `DepCmd`), or
||| produce a counter-proof for why it cannot be one.
public export
isDepEdge : (e : DSAEdge) -> Dec (IsDepEdge e)
isDepEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = Yes ItIsDepEdge
isDepEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
isDepEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
isDepEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
isDepEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
isDepEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
isDepEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
isDepEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

--------------------
-- Prod-edge only --
--------------------

public export
data IsProdEdge : DSAEdge -> Type where
  ItIsProdEdge : IsProdEdge (MkDSAEdge (ProdCmd _ _) _ _)

public export
Uninhabited (IsProdEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsProdEdge impossible
public export
Uninhabited (IsProdEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsProdEdge impossible

------------------------
-- Take-dep edge only --
------------------------

public export
data IsTDEdge : DSAEdge -> Type where
  ItIsTDEdge : IsTDEdge (MkDSAEdge (TDCmd _ _ _) _ _)

public export
Uninhabited (IsTDEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsTDEdge impossible
public export
Uninhabited (IsTDEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsTDEdge impossible

||| Prove that an edge is a take-dep edge (i.e. it contains a `TDCmd`), or
||| produce a counter-proof for why it cannot be one.
public export
isTDEdge : (e : DSAEdge) -> Dec (IsTDEdge e)
isTDEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = Yes ItIsTDEdge
isTDEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
isTDEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
isTDEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
isTDEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
isTDEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
isTDEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd
isTDEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-------------------------
-- Take-prod edge only --
-------------------------

public export
data IsTPEdge : DSAEdge -> Type where
  ItIsTPEdge : IsTPEdge (MkDSAEdge (TPCmd _ _ _) _ _)

public export
Uninhabited (IsTPEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsTPEdge impossible
public export
Uninhabited (IsTPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsTPEdge impossible

------------------------
-- Dep-prod edge only --
------------------------

public export
data IsDPEdge : DSAEdge -> Type where
  ItIsDPEdge : IsDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)

public export
Uninhabited (IsDPEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsDPEdge impossible
public export
Uninhabited (IsDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)) where
  uninhabited ItIsDPEdge impossible

||| Prove that an edge is a dep-prod edge (i.e. it contains a `DPCmd`), or
||| produce a counter-proof for why it cannot be one.
public export
isDPEdge : (e : DSAEdge) -> Dec (IsDPEdge e)
isDPEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = Yes ItIsDPEdge
isDPEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
isDPEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
isDPEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
isDPEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
isDPEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
isDPEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
isDPEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = No absurd

-----------------------------
-- Take-dep-prod edge only --
-----------------------------

public export
data IsTDPEdge : DSAEdge -> Type where
  ItIsTDPEdge : IsTDPEdge (MkDSAEdge (TDPCmd _ _ _ _) _ _)

public export
Uninhabited (IsTDPEdge (MkDSAEdge (PlainCmd _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (TakeCmd _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (DepCmd _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (ProdCmd _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (TDCmd _ _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (TPCmd _ _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible
public export
Uninhabited (IsTDPEdge (MkDSAEdge (DPCmd _ _ _) _ _)) where
  uninhabited ItIsTDPEdge impossible

||| Prove that an edge is a take-dep-prod edge (i.e. it contains a `TDPCmd`), or
||| produce a counter-proof for why it cannot be one.
public export
isTDPEdge : (e : DSAEdge) -> Dec (IsTDPEdge e)
isTDPEdge e@(MkDSAEdge (TDPCmd _ _ _ _) _ _) = Yes ItIsTDPEdge
isTDPEdge e@(MkDSAEdge (PlainCmd _) _ _)     = No absurd
isTDPEdge e@(MkDSAEdge (TakeCmd _ _) _ _)    = No absurd
isTDPEdge e@(MkDSAEdge (DepCmd _ _) _ _)     = No absurd
isTDPEdge e@(MkDSAEdge (ProdCmd _ _) _ _)    = No absurd
isTDPEdge e@(MkDSAEdge (TDCmd _ _ _) _ _)    = No absurd
isTDPEdge e@(MkDSAEdge (TPCmd _ _ _) _ _)    = No absurd
isTDPEdge e@(MkDSAEdge (DPCmd _ _ _) _ _)    = No absurd

-----------------------------
-- Non-depedent edges only --
-----------------------------

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

--------------------------------------
-- Non-plain AND non-dependent only --
--------------------------------------

||| A proof that the given edge is not a dependent edge (i.e. it always goes to
||| the same state), AND that the edge is not a plain edge (i.e. it _does_ do
||| something interesting, for example producing a value).
||| Second attempt at `NotPlainNonDep`...
public export
data NPND2 : Subset DSAEdge (Not . IsPlainEdge) -> Type where
  ProdNonDep : NPND2 (Element (MkDSAEdge (ProdCmd _ _) _ _) nonPlainPrf)
  TakeNonDep : NPND2 (Element (MkDSAEdge (TakeCmd _ _) _ _) nonPlainPrf)
  TPNonDep   : NPND2 (Element (MkDSAEdge (TPCmd _ _ _) _ _) nonPlainPrf)

public export
Uninhabited (NPND2 (Element (MkDSAEdge (DepCmd _ _) _ _) nonPlainPrf)) where
  uninhabited ProdNonDep impossible
  uninhabited TakeNonDep impossible
  uninhabited TPNonDep impossible

public export
Uninhabited (NPND2 (Element (MkDSAEdge (TDCmd _ _ _) _ _) nonPlainPrf)) where
  uninhabited ProdNonDep impossible
  uninhabited TakeNonDep impossible
  uninhabited TPNonDep impossible

public export
Uninhabited (NPND2 (Element (MkDSAEdge (DPCmd _ _ _) _ _) nonPlainPrf)) where
  uninhabited ProdNonDep impossible
  uninhabited TakeNonDep impossible
  uninhabited TPNonDep impossible

public export
Uninhabited (NPND2 (Element (MkDSAEdge (TDPCmd _ _ _ _) _ _) nonPlainPrf)) where
  uninhabited ProdNonDep impossible
  uninhabited TakeNonDep impossible
  uninhabited TPNonDep impossible

-------------------
-- Dec functions --
-------------------

public export
isNPND2 : (s : Subset DSAEdge (Not . IsPlainEdge)) -> Dec (NPND2 s)
isNPND2 (Element (MkDSAEdge (PlainCmd _) _ _) snd)     = void $ snd EdgeIsPlain
isNPND2 (Element (MkDSAEdge (DepCmd _ _) _ _) snd)     = No absurd
isNPND2 (Element (MkDSAEdge (TDCmd _ _ _) _ _) snd)    = No absurd
isNPND2 (Element (MkDSAEdge (DPCmd _ _ _) _ _) snd)    = No absurd
isNPND2 (Element (MkDSAEdge (TDPCmd _ _ _ _) _ _) snd) = No absurd
isNPND2 (Element (MkDSAEdge (TakeCmd _ _) _ _) snd)    = Yes TakeNonDep
isNPND2 (Element (MkDSAEdge (ProdCmd _ _) _ _) snd)    = Yes ProdNonDep
isNPND2 (Element (MkDSAEdge (TPCmd _ _ _) _ _) snd)    = Yes TPNonDep

