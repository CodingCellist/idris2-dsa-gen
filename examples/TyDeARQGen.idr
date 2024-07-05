data ARQState
  = Acked ?sn_type ?an_type
  | Waiting ?sn_type
  | Ready ?sn_type

data WaitRes
  = Ack ?an_type
  | Timeout

data ARQCmd : (resTy : Type) -> ARQState -> (resTy -> ARQState) -> Type where


  Retry : (NotEqual an sn) -> ARQCmd () (Acked sn an) (const (Ready sn))
  Proceed : (Equal an sn) -> ARQCmd () (Acked sn an) (const (Ready sn))
  Send : (Pkt) -> ARQCmd () (Ready sn) (const (Waiting sn))
  Wait : ARQCmd (WaitRes) (Waiting sn) (\case (Ack an) => (Acked sn an); (Timeout) => (Ready sn))

  Pure : (res : resTy) -> ARQCmd resTy (state_fn res) state_fn

  (>>=) :  ARQCmd resTy state_1 state2_fn
        -> (contn : (res : resTy) -> ARQCmd cResTy (state2_fn res) state3_fn)
        -> ARQCmd cResTy state_1 state3_fn
