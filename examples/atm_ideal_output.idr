-- Idris2

import Data.Vect

data State = Ready
           | CardInserted
           | Session

data CheckPINRes = Incorrect
                 | Correct

data HasCard : State -> Type where
  HasCardInserted : HasCard CardInserted
  HasSession      : HasCard Session

data CMD : (ty : Type) -> State -> (ty -> State) -> Type where
  -- EZ
  InsertCard : CMD () Ready (const CardInserted)
  Dispense   : CMD () Session (const Session)
  GetPIN     : CMD () CardInserted (const CardInserted)

  -- Might be more difficult
  CheckPIN   : (Vect 4 Nat) ->
               CMD CheckPINRes CardInserted (\cpr => case cpr of
                                                          Incorrect => CardInserted
                                                          Correct => Session)

  EjectCard  : {auto prf : HasCard state} -> CMD () state (const Ready)

  -- EZPZ: constant
  Pure       : (res : ty) -> CMD ty (state_fn res) state_fn
  (>>=)      : CMD res1t state1 s1TOs2_fn ->
               ((res : res1t) -> CMD res2t (s1TOs2_fn res) s2TOs3_fn) ->
               CMD res2t state1 s2TOs3_fn

