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

s1s2 : RegEdge
s1s2 = MkRegEdge (MkLabel "InsertCard") atm_s1 atm_s2

s2s2 : RegEdge
s2s2 = MkRegEdge (MkLabel "GetPIN") atm_s2 atm_s2

s2dep : DepEdge
s2dep = MkDepEdge (MkLabel "CheckPin")
                  atm_s2
                  [MkDepRes "Incorrect" atm_s2, MkDepRes "Correct" atm_s3]

s3s3 : RegEdge
s3s3 = MkRegEdge (MkLabel "Dispense") atm_s3 atm_s3

anyS1 : RegEdge
anyS1 = MkRegEdge (MkLabel "EjectCard") any atm_s1

export
atm : DSA
atm = MkDSA "ATM"
            [atm_s1, atm_s2, atm_s3]
            [s1s2, s2s2, s3s3, anyS1]
            [s2dep]
```

and then used to generate Idris through the (currently unsafe) `unsafeGenIdris`
function, resulting in the following output:

```bash
$ idris2 -p contrib -p dot-parse DSAGen.idr --exec atmTest
```

```idris
-- /!\ UNSAFELY GENERATED /!\ -- 

data ATMState = Ready | CardInserted | Session

data CheckPinRes = Incorrect | Correct

data ATMCmd : (ty : Type)  -> ATMState -> (ty -> ATMState) -> Type where

  InsertCard : ATMCmd () Ready (const CardInserted)
  GetPIN : ATMCmd () CardInserted (const CardInserted)
  Dispense : ATMCmd () Session (const Session)
  EjectCard : ATMCmd () state (const Ready)


  CheckPin : ATMCmd CheckPinRes CardInserted (\depRes => case depRes of Incorrect => CardInserted; Correct => Session)


  Pure : (res : ty) -> ATMCmd ty (state_fn res) state_fn

  (>>=) :  ATMCmd a state1 state2_fn
        -> ((res : a) -> ATMCmd b (state2_fn res) state3_fn)
        -> ATMCmd b state1 state3_fn
```

It is not the prettiest, but it type-checks and you would be able to program
parts of Ch 14 using the result.

Generating Idris source code from `.gv` files is almost done. There are just
some wrinkles in terms of multiple transitions (e.g. a transition that can be
done from any state) which I need to iron out. Soon (TM).

# LICENSE
This work is licensed under GPL-2.0.

