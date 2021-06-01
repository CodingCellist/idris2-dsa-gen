# idris2-dsa-gen
Idris2 code based on Dependent State Automata diagrams.

# What?
If you have followed the Type Driven Development with Idris book, you may have
spotted some patterns in chapter 14 in terms of modelling dependent state
automata in Idris. This project attempts to auto-generate the Idris2 source-code
for these based on a DOT (`.gv`) file.

# Does it work?

Yes! The following example (from the TDD book, Ch 14), can be modelled:

```idris
any : State
any = MkState (MkLabel "state")

atm_s1 : State
atm_s1 = MkState (MkLabel "Ready")

atm_s2 : State
atm_s2 = MkState (MkLabel "CardInserted")

atm_s3 : State
atm_s3 = MkState (MkLabel "Session")

s1s2 : Edge
s1s2 = RegAction (MkLabel "InsertCard") atm_s1 atm_s2

s2s2 : Edge
s2s2 = RegAction (MkLabel "GetPIN") atm_s2 atm_s2

s2dep : Edge
s2dep = DepAction (MkLabel "CheckPin")
                  atm_s2
                  [MkDepRes "Incorrect" atm_s2, MkDepRes "Correct" atm_s3]

s3s3 : Edge
s3s3 = RegAction (MkLabel "Dispense") atm_s3 atm_s3

anyS1 : Edge
anyS1 = RegAction (MkLabel "EjectCard") any atm_s1

export
atm : DSA
atm = MkDSA [atm_s1, atm_s2, atm_s3]
            [s1s2, s2s2, s2dep, s3s3, anyS1]
```

and then used to generate Idris through the (currently unsafe) `unsafeGenIdris`
function, resulting in the following output:

```bash
$ idris2 -p contrib DSAGen.idr --exec atmTest
```

```idris
-- UNSAFELY GENERATED! --

data State = Ready | CardInserted | Session

data CheckPinRes = Incorrect | Correct

data Cmd : (ty : Type) -> State -> (ty -> State) -> Type where
  InsertCard : Cmd () Ready (const CardInserted)
  GetPIN : Cmd () CardInserted (const CardInserted)
  Dispense : Cmd () Session (const Session)
  EjectCard : Cmd () state (const Ready)
  CheckPin : Cmd CheckPinRes CardInserted (\depRes => case depRes of Incorrect => CardInserted; Correct => Session)


  Pure : (res : ty) -> Cmd ty (state_fn res) state_fn

  (>>=) : Cmd a state1 state2_fn
        -> ((res : a) -> Cmd b (state2_fn res) state3_fn)
        -> Cmd b state1 state3_fn
```

It is not the prettiest, but it type-checks and you would be able to program
parts of Ch 14 using the result.

# License
This work is licensed under GPL-2.0.

