data ATMState
  = Session
  | CardInserted
  | Ready

data CheckPINRes
  = Incorrect
  | Correct

data ATMCmd : (resTy : Type) -> ATMState -> (resTy -> ATMState) -> Type where

  InsertCard : ATMCmd () (Ready) (const (CardInserted))
  Dispense : ATMCmd () (Session) (const (Session))
  GetPIN : ATMCmd (PIN) (CardInserted) (const (CardInserted))
  CheckPIN : ATMCmd (CheckPINRes) (CardInserted) (\case (Incorrect) => (CardInserted); (Correct) => (Session))

  EjectCard : ATMCmd () anyState (const (Ready))

  Pure : (res : resTy) -> ATMCmd resTy (state_fn res) state_fn

  (>>=) :  ATMCmd resTy state_1 state2_fn
        -> (contn : (res : resTy) -> ATMCmd cResTy (state2_fn res) state3_fn)
        -> ATMCmd cResTy state_1 state3_fn
