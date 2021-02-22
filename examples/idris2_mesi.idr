-- Idris2

import Data.Vect

-- bits are either 0 or 1
data Bit = ZERO
         | ONE

-- bytes are 8 bits
Byte : Type
Byte = Vect 8 Bit

-- 64-byte cache lines
CacheLine : Type
CacheLine = Vect 64 Byte

-- based on https://upload.wikimedia.org/wikipedia/commons/c/c1/Diagrama_MESI.GIF

data State = Modified
           | Exclusive
           | Shared
           | Invalid

-- define a type for permitted combinations
data IsPermitted : State -> State -> Type where
  MI : IsPermitted Modified  Invalid
  EI : IsPermitted Exclusive Invalid
  S2 : IsPermitted Shared    Shared
  SI : IsPermitted Shared    Invalid
  II : IsPermitted Invalid   state

data CacheCopyStatus = Valid
                     | None

data Transaction : (ty : Type) -> State -> (ty -> State) -> Type where
  BusRdM  : Transaction () Modified  (const Shared)
  BusRdXM : Transaction () Modified  (const Invalid)

  BusRdE  : Transaction () Exclusive (const Shared)
  BusRdXE : Transaction () Exclusive (const Invalid)

  BusUpgr : Transaction () Shared    (const Invalid)

  PrRdI   : CacheLine ->
            Transaction CacheCopyStatus Invalid
              (\ccs => case ccs of
                            Valid => Shared
                            None => Exclusive)

  PrWrI   : Transaction () Invalid   (const Modified)

  PrRdE   : Transaction () Exclusive (const Exclusive)
  PrWrE   : Transaction () Exclusive (const Modified)

  PrRdS   : Transaction () Shared    (const Shared)
  PrWrS   : Transaction () Shared    (const Modified)

  PrRdM   : Transaction () Modified  (const Modified)
  
  Pure    : (res : ty) -> Transaction ty (state_fn res) state_fn

  (>>=)   : Transaction res1t state1 s1TOs2_fn ->
            ((res1 : res1t) -> Transaction res2t (s1TOs2_fn res1) s2TOs3_fn) ->
            Transaction res2t state1 s2TOs3_fn

