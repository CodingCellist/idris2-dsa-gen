data MESIState
  = E
  | S
  | I
  | M

data MESICmd : (resTy : Type) -> MESIState -> (resTy -> MESIState) -> Type where

  BusRd_Flush : MESICmd () (M) (const (S))
  BusRd_ : MESICmd () (E) (const (S))
  PrRd_ : MESICmd () (M) (const (M))
  PrWr_ : MESICmd () (M) (const (M))
  PrWr_ : MESICmd () (E) (const (M))
  PrRd_ : MESICmd () (E) (const (E))
  PrWr_BusRdX : MESICmd () (S) (const (M))
  PrRd_ : MESICmd () (S) (const (S))
  PrRd_BusRdS : MESICmd () (I) (const (S))
  PrRd_BusRdS : MESICmd () (I) (const (E))
  ProcWr_BusRdX : MESICmd () (I) (const (M))



  BusRdX_Flush : MESICmd () anyState (const (I))

  Pure : (res : resTy) -> MESICmd resTy (state_fn res) state_fn

  (>>=) :  MESICmd resTy state_1 state2_fn
        -> (contn : (res : resTy) -> MESICmd cResTy (state2_fn res) state3_fn)
        -> MESICmd cResTy state_1 state3_fn
