module DSAGen.Idris2CodeGen

import DSAGen.DSLv2

------------------------
-- Static definitions --
------------------------

||| Pure is always defined for DSAs in the same way.
pure : (dsaName : String) -> String
pure dsaName =
  "Pure : (res : resTy) -> \{dsaName}Cmd resTy (state_fn res) state_fn"

||| Bind (>>=) is always defined for DSAs in the same way.
bind : (dsaName : String) -> String
bind dsaName =
  "(>>=) :  \{dsaName}Cmd resTy state_1 state2_fn\n" ++
  "      -> (contn : (res : resTy) -> \{dsaName}Cmd cResTy (state2_fn res) state3_fn)\n" ++
  "      -> \{dsaName}Cmd cResTy state_1 state3_fn"


------------------------
-- Type-gen functions --
------------------------

||| The data type for DSA states is based on the DSA's name.
stateType : (dsaName : String) -> String
stateType dsaName =
  "data \{dsaName}State : Type where"

||| The data type for DSA commands is based on the DSA's name and carries the
||| result type, the current state, and a function from the result type to the
||| next state.
cmdType : (dsaName : String) -> String
cmdType dsaName =
  "data \{dsaName}Cmd : (resTy : Type) -> \{dsaName}State -> (resTy -> \{dsaName}State) -> Type where"


-----------------------
-- Generating Idris2 --
-----------------------

||| Convert the given `DSA` to Idris2 source code.
export
toIdris2 : DSAv2 -> String
toIdris2 (MkDSAv2 dsaName states edges universalEdges) = ?toIdris_rhs_0

