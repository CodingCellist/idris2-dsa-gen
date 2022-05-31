module DSAGen.Idris2CodeGen

import DSAGen.DSLv2

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

||| Convert the given `DSA` to Idris2 source code.
export
toIdris : DSAv2 -> String
toIdris (MkDSAv2 dsaName states edges universalEdges) = ?toIdris_rhs_0

