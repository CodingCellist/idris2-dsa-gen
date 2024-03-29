module DSAGen.Idris2CodeGen

import DSAGen.DSLv2
import DSAGen.Parser
import DSAGen.Constraints

import Data.DPair
import Data.String
import Data.List.Quantifiers

%default covering

--------------------------------------------------------------------------------
-- HELPERS
--------------------------------------------------------------------------------

---------------
-- Constants --
---------------

||| The number of spaces to a tab in the CG.d output.
tabWidth : Nat
tabWidth = 2

----------------
-- Data types --
----------------

||| A dependent result links a case of the edge's dependency value to the
||| corresponding state.
record DepRes where
  constructor MkDepRes
  depCase : DepArg
  caseTo : Subset Value IsDataVal

||| The result of accumulating all the dependent edges of a depedent command.
record DepCmdAcc where
  constructor MkDCAcc
  ||| The name of the command.
  cmd : String

  ||| The state the command starts at.
  from : Subset Value IsDataVal

  ||| The list of value-state pairs that the command can dependently go to.
  cases : List1 DepRes

||| A produced value on a dependent edge contains the dependent case and
||| destination, along with the result.
record ProdDepRes where
  constructor MkProdDepRes
  depCase : DepArg
  caseTo : Subset Value IsDataVal
  res : ProdArg

||| The result of accumulating all the dependent cases of a dep-prod command.
record DPCmdAcc where
  constructor MkDPAcc
  ||| The name of the command.
  cmd : String

  ||| The state the command starts at.
  from : Subset Value IsDataVal

  ||| The list of value-state pairs that the command can dependently go to.
  cases : List1 ProdDepRes

---------------------------
-- Accumulator functions --
---------------------------

||| Initialise the dependent edge accumulator using the given dependent edge.
total
initDEAcc :  (iDepEdge : Subset DSAEdge IsDepEdge)
          -> DepCmdAcc
initDEAcc (Element (MkDSAEdge (DepCmd cmd depCase) from to) _) =
  MkDCAcc cmd from (singleton $ MkDepRes depCase to)

||| Add the dependent edge's case-dest pair to the accumulator.
|||
||| @ acc The dependent edge accumulator.
||| @ depEdge The edge whose case-dest pair to add.
total
addDECase :  (acc : DepCmdAcc)
          -> (depEdge : Subset DSAEdge IsDepEdge)
          -> DepCmdAcc
addDECase acc (Element (MkDSAEdge (DepCmd cmd depCase) from to) _) =
  { cases $= cons (MkDepRes depCase to) } acc


||| Accumulate the list of dependent edges into a single data-structure keeping
||| track of the dependent results.
||| /!\ DOES NOT CHECK NAME/CMD EQUALITY /!\
total
accDEs : (des : List1 (Subset DSAEdge IsDepEdge)) -> DepCmdAcc
accDEs (head@(Element (MkDSAEdge (DepCmd cmd depCase) from to) _) ::: tail) =
  foldl addDECase (initDEAcc head) tail

||| Accumulate all the unique dependent edges in the given non-empty list,
||| returning the resulting accumulated/complete dependent edges.
accAllDEs : List1 (Subset DSAEdge IsDepEdge) -> List1 DepCmdAcc
accAllDEs (de1 ::: tail) =
  case partition (deCmdEq de1) tail of
       (de1s, []) => singleton $ accDEs (de1 ::: de1s)
       (de1s, de2s@(_ :: _)) =>
            cons (accDEs (de1 ::: de1s)) (accAllDEs $ toList1 de2s)
  where
    deCmdEq : (de1, de2 : Subset DSAEdge IsDepEdge) -> Bool
    deCmdEq (Element (MkDSAEdge (DepCmd cmd1 _) _ _) _) (Element (MkDSAEdge (DepCmd cmd2 _) _ _) _) =
      cmd1 == cmd2

-----------------
-- Misc. utils --
-----------------

||| If the given string starts with an open-parenthesis, then removes the first
||| and last character of the string (i.e. de-parenthesises it).
|||
||| This is because data constructor declarations in Idris may not be
||| parenthesised
total
cleanDataConsDecl : (rawDCD : String) -> String
cleanDataConsDecl rawDCD =
  case asList rawDCD of
       ('(' :: rest) => substr 1 (minus (length rawDCD) 2) rawDCD
       _ => rawDCD

||| Indent and line-separate each of the strings in the given list, returning
||| the resulting appended string.
%inline
indentAndLineSep : List String -> String
indentAndLineSep = joinBy "\n" . map (indent tabWidth)

||| Given a predicate and a list of elements, return the list of elements that
||| satisfy the predicate, paired with the proof that they satisfy it.
subsetFilter : ((x : a) -> Dec (p x)) -> (xs : List a) -> List (Subset a p)
subsetFilter f [] = []
subsetFilter f (x :: xs) with (f x)
  _ | (Yes prf) = (Element x prf) :: subsetFilter f xs
  _ | (No contra) = subsetFilter f xs

||| Convert a `Split` of a property into the `Subset` of only the elements which
||| did not satisfy the predicate used for the `Split`. This forgets the
||| relation to the interleaving list that the `Split` contains.
%inline
-- note: adding {0 l : List a} significantly speeds things up (unification slow?)
splitNawsSubset : {0 l : List a} -> (s : Split p l) -> List (Subset a (Not . p))
splitNawsSubset s = pushIn s.naws s.contras

--------------------------------------------------------------------------------
-- INTERFACES --
--------------------------------------------------------------------------------

export
covering
Show DepRes where
  show dr =
    "{ DepRes " ++ show dr.depCase ++ " " ++ show dr.caseTo ++ " }"

export
covering
Show DepCmdAcc where
  show dca =
    "{ DepCmdAcc " ++ (joinBy " " $ [show dca.cmd, show dca.from, show dca.cases]) ++ " }"


--------------------------------------------------------------------------------
-- CODE GEN
--------------------------------------------------------------------------------

------------------------
-- Static definitions --
------------------------

||| No result is defined as Unit.
total
noRes : String
noRes = "()"

||| Pure is always defined for DSAs in the same way.
total
pureCmd : (dsaName : String) -> String
pureCmd dsaName = indent tabWidth $
  "Pure : (res : resTy) -> \{dsaName}Cmd resTy (state_fn res) state_fn"

||| Bind (>>=) is always defined for DSAs in the same way.
total
bindCmd : (dsaName : String) -> String
bindCmd dsaName = concat $ map (indent tabWidth) $
  [ "(>>=) :  \{dsaName}Cmd resTy state_1 state2_fn\n"
  , "      -> (contn : (res : resTy) -> \{dsaName}Cmd cResTy (state2_fn res) state3_fn)\n"
  , "      -> \{dsaName}Cmd cResTy state_1 state3_fn"
  ]


------------------------
-- Type-gen functions --
------------------------

||| The data type for DSA commands is based on the DSA's name and carries the
||| result type, the current state, and a function from the result type to the
||| next state.
total
genCmdDecl : (dsaName : String) -> String
genCmdDecl dsaName =
  "data \{dsaName}Cmd : (resTy : Type) -> \{dsaName}State -> (resTy -> \{dsaName}State) -> Type where"


||| The barebones command type string
total
commandTy : (dsaName : String) -> String
commandTy dsaName = "\{dsaName}Cmd"

||| The barebones state type string
total
stateTy : (dsaName : String) -> String
stateTy dsaName = "\{dsaName}State"


----------------
-- DataVal CG --
----------------

||| /!\ USE AS PART OF FUNCTIONS ONLY /!\
|||
||| Internal values are allowed to have plain Idris names, since these get
||| interpreted as implicit arguments.
|||
||| A value is one of:
|||   - an Idris name
|||   - an integer literal
|||   - a data constructor, optionally taking some values as arguments
|||   - the addition of two values
|||   - a tuple of values
genInternalValue : Value -> String
-- ez
genInternalValue (IdrName n) = n
genInternalValue (LitVal lit) = show lit
genInternalValue (DataVal dc Nothing) = "(\{dc})"
-- funky
genInternalValue (DataVal dc (Just args)) =
  let argString = joinBy " " (genInternalValue <$> toList args)
  in "(\{dc} \{argString})"

genInternalValue (AddExpr num addend) =
  let numStr = genInternalValue num
      addendStr = genInternalValue addend
  in "(\{numStr} + \{addendStr})"

genInternalValue (Tuple fst snd) = "(\{genInternalValue fst}, \{genInternalValue snd})"

||| /!\ USE AS PART OF FUNCTIONS ONLY /!\
|||
||| Top-level values differ slightly from internal ones in that they must be
||| types! As such, if we do not know the type of a thing, we generate a hole
||| instead.
|||
||| A value is one of:
|||   - an Idris name (these become type holes)
|||   - an integer literal
|||   - a data constructor, optionally taking some values as arguments
|||   - the addition of two values
|||   - a tuple of values
genTopLevelValue : Value -> String
-- ez
genTopLevelValue (IdrName n) = "?\{n}_type"
genTopLevelValue (LitVal lit) = show lit
genTopLevelValue (DataVal dc Nothing) = "(\{dc})"
-- funky
genTopLevelValue (DataVal dc (Just args)) =
  let argString = joinBy " " (genTopLevelValue <$> toList args)
  in "(\{dc} \{argString})"

genTopLevelValue (AddExpr num addend) =
  let numStr = genTopLevelValue num
      addendStr = genTopLevelValue addend
  in "(\{numStr} + \{addendStr})"

genTopLevelValue (Tuple fst snd) = "(\{genTopLevelValue fst}, \{genTopLevelValue snd})"

||| A data value is a data constructor, optionally taking some arguments.
|||
||| @ dcTy a string representing the return type of the data constructor
genDataConsDecl : (dcTy : String) -> Subset Value IsDataVal -> String
genDataConsDecl dcTy (Element (DataVal dc Nothing) isDV) = "\{dc} : \{dcTy}"
genDataConsDecl dcTy (Element (DataVal dc (Just args)) isDV) =
  let argStrings = map genInternalValue args
      argString = joinBy " -> " $ toList argStrings
  in "\{dc} : \{argString} -> \{dcTy}"

-----------
-- Edges --
-----------

||| A plain command is a constructor which takes no arguments and always goes to
||| the same state (i.e. no dependent transition).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the plain command.
genPlainEdge : (dsaName : String) -> (edge : Subset DSAEdge IsPlainEdge) -> String
genPlainEdge dsaName (Element (MkDSAEdge (PlainCmd cmd) from to) isPlain) =
  let cmdStart = commandTy dsaName
      fromState = genInternalValue from.fst
      toState = genInternalValue to.fst
  in "\{cmd} : \{cmdStart} \{noRes} \{fromState} (const \{toState})"

||| Generate all the plain edge definitions in the DSA, properly indented and
||| line-separated.
|||
||| @ dsaName The name of the DSA that the plain edges belong to.
||| @ plainEdges The edges which are definitely plain.
||| @ edgesArePlain A proof that the edges are plain.
genPlainEdges :  (dsaName : String)
              -> (plainEdges : List DSAEdge)
              -> (0 edgesArePlain : All IsPlainEdge plainEdges)
              -> String
genPlainEdges dsaName plainEdges edgesArePlain =
  indentAndLineSep $ map (genPlainEdge dsaName) plainEdgeSubsets
  where
    -- we need to bundle the proofs for `genPlainEdge`
    plainEdgeSubsets : List (Subset DSAEdge IsPlainEdge)
    plainEdgeSubsets = pushIn plainEdges edgesArePlain

||| A command which takes a value is a function from the argument to a
||| constructor which produces nothing and goes to a constant state (or it would
||| be a take-dep command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the take command
genTakeEdge :  (dsaName : String)
            -> (edge : DSAEdge)
            -> {auto 0 constraint : IsTakeEdge edge}
            -> String
genTakeEdge dsaName (MkDSAEdge (TakeCmd cmd (Takes arg)) from to) =
  let cmdTyStart = commandTy dsaName
      argStr = genInternalValue arg
      fromState = genInternalValue from.fst
      toState = genInternalValue to.fst
  in "\{cmd} : \{argStr} -> \{cmdTyStart} \{noRes} \{fromState} (const \{toState})"

||| A command which produces a value is a constructor with the result as the
||| return type, and it must always go to the same state (or it would be a
||| prod-dep command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the prod command
genProdEdge :  (dsaName : String)
            -> (edge : DSAEdge)
            -> {auto 0 constraint : IsProdEdge edge}
            -> String
genProdEdge dsaName (MkDSAEdge (ProdCmd cmd (Produce val)) from to) =
  let cmdTyStart = commandTy dsaName
      resStr = genInternalValue val
      fromState = genInternalValue from.fst
      toState = genInternalValue to.fst
  in "\{cmd} : \{cmdTyStart} \{resStr} \{fromState} (const \{toState})"

||| A command which takes and produces a value is a function from the argument
||| to a constructor with the result as the return type, and it must always go
||| to the same state (or it would be a take-dep-prod command).
|||
||| @ dsaName The name of the DSA that the command is part of.
||| @ edge The `DSAEdge` containing the description of the take-prod command.
genTPEdge :  (dsaName : String)
          -> (edge : DSAEdge)
          -> {auto 0 constraint : IsTPEdge edge}
          -> String
genTPEdge dsaName (MkDSAEdge (TPCmd cmd (Takes arg) (Produce val)) from to) =
  let cmdTyStart = commandTy dsaName
      argStr = genInternalValue arg
      resStr = genInternalValue val
      fromState = genInternalValue from.fst
      toState = genInternalValue to.fst
  in "\{cmd} : \{argStr} -> \{cmdTyStart} \{resStr} \{fromState} (const \{toState})"

||| Generate the `case` expression which represents the transition function of
||| the given dependent command.
|||
||| @ completeDC The entire dependent command.
genDepCmdCaseExpr : (completeDC : DepCmdAcc) -> String
genDepCmdCaseExpr (MkDCAcc _ _ cases) =
  "(\\case " ++ joinBy "; " (toList $ map genCase cases) ++ ")"
  where
    -- the LHS (i.e. pattern) of the case expression
    genCaseLHS : DepArg -> String
    genCaseLHS (DepsOn val) = genInternalValue val

    -- the RHS (i.e. destination state) of the case-match
    genCaseRHS : Subset Value IsDataVal -> String
    genCaseRHS depDest = genInternalValue depDest.fst

    genCase : DepRes -> String
    genCase dr = "\{genCaseLHS dr.depCase} => \{genCaseRHS dr.caseTo}"

||| Generate the data constructor representing the depedent command in a DSA.
|||
||| @ dsaName The name of the DSA in which the depedent command occurs.
||| @ completeDC The entire dependent command.
genDepCmdBody : (dsaName : String) -> (completeDC : DepCmdAcc) -> String
genDepCmdBody dsaName completeDC =
  "\{completeDC.cmd} : \{cmdStart} \{resTy} \{fromState} \{toCaseFn}"
  where
    -- the start of the command declaration
    cmdStart : String
    cmdStart = commandTy dsaName

    -- the type of the result (see the where-block in `genDepRess`)
    resTy : String
    resTy = "(\{completeDC.cmd}Res)"

    fromState : String
    fromState = genInternalValue completeDC.from.fst

    -- the destination state is a dep.t function (that's kinda the whole idea)
    toCaseFn : String
    toCaseFn = genDepCmdCaseExpr completeDC

||| Generate the data constructor representing a non-plain, non-dependent edge
||| (i.e. either a Take, Prod, or Take-Prod edge).
|||
||| @ dsaName The name of the DSA in which the edge occurs.
||| @ npndEdge The non-plain, non-dependent edge; along with its proofs.
genNotPlainNonDepEdge :  (dsaName : String)
                      -> (npndEdge : Subset (Subset DSAEdge (Not . IsPlainEdge)) NPND)
                      -> String
genNotPlainNonDepEdge dsaName (Element (Element (MkDSAEdge (PlainCmd _) _ _) np) _) =
  void $ np EdgeIsPlain
genNotPlainNonDepEdge dsaName (Element (Element (MkDSAEdge (DepCmd _ _) _ _) _) npnd) =
  void $ absurd npnd
genNotPlainNonDepEdge dsaName (Element (Element (MkDSAEdge (TDCmd _ _ _) _ _) _) npnd) =
  void $ absurd npnd
genNotPlainNonDepEdge dsaName (Element (Element (MkDSAEdge (DPCmd _ _ _) _ _) _) npnd) =
  void $ absurd npnd
genNotPlainNonDepEdge dsaName (Element (Element (MkDSAEdge (TDPCmd _ _ _ _) _ _) _) npnd) =
  void $ absurd npnd
genNotPlainNonDepEdge dsaName (Element (Element te@(MkDSAEdge (TakeCmd cmd arg) from to) _) _) =
  genTakeEdge dsaName te
genNotPlainNonDepEdge dsaName (Element (Element pe@(MkDSAEdge (ProdCmd cmd res) from to) _) _) =
  genProdEdge dsaName pe
genNotPlainNonDepEdge dsaName (Element (Element tpe@(MkDSAEdge (TPCmd cmd arg res) from to) _) _) =
  genTPEdge dsaName tpe

||| Generate all the non-plain, non-dependent edge definitions, properly
||| indenting and line-separating them along the way.
|||
||| @ dsaName The name of the DSA that the edges are part of.
||| @ npndEs The non-plain, non-dependent edges to generate, along with their
|||          proofs.
||| See-also: `genNotPlainNonDepEdge`
genNotPlainNonDepEdges :  (dsaName : String)
                       -> (npndEs : List (Subset (Subset DSAEdge (Not . IsPlainEdge)) NPND))
                       -> String
genNotPlainNonDepEdges dsaName npndEs =
  indentAndLineSep $ map (genNotPlainNonDepEdge dsaName) npndEs

||| Partition, accumulate, and generate all the non-plain, dependent edge
||| definitions, properly indenting and line-separating them along the way.
genNonPlainDependentEdges :  (dsaName : String)
                          -> (npdEs : List (Subset (Subset DSAEdge (Not . IsPlainEdge)) (Not . NPND)))
                          -> String
genNonPlainDependentEdges dsaName npdEs =
  joinBy "\n" $ filter (/= "") $ [depDecls, tdDecls, dpDecls, tdpDecls]
  where
    -- forget the proofs/constraints associated with the npdEs list;
    -- should be fine, since the exterior (i.e. the function you can call) is
    -- still constrained
    justTheNPDEs : List DSAEdge
    justTheNPDEs = map (Subset.fst . Subset.fst) npdEs

    -- all the dependent commands, indented and line-separated
    depDecls : String
    depDecls =
      case subsetFilter isDepEdge justTheNPDEs of
           [] => ""
           des@(_ :: _) => indentAndLineSep $
               map (genDepCmdBody dsaName) $ toList (accAllDEs $ toList1 des)

    -- all the take-dep commands, indented and line-separated
    tdDecls : String
    tdDecls =
      case subsetFilter isTDEdge justTheNPDEs of
           [] => ""
           tdEs@(_ :: _) => ?takedep_cg_not_implemented_sorry

    -- all the dep-prod commands, indented and line-separated
    dpDecls : String
    dpDecls =
      case subsetFilter isDPEdge justTheNPDEs of
           [] => ""
           dpEs@(_ :: _) => ?depprod_cg_not_implemented_sorry

    -- all the take-dep-prod commands, indented and line-separated
    tdpDecls : String
    tdpDecls =
      case subsetFilter isTDPEdge justTheNPDEs of
           [] => ""
           tpdEs@(_ :: _) => ?takedepprod_cg_not_implemented_sorry

-----------------------
-- Universal Edge CG --
-----------------------

||| A universal edge can be taken from anywhere in the DSA, and so does not name
||| a specific state in its command definition.
genUniversalEdge : (dsaName : String) -> (ue : UniversalEdge) -> String
genUniversalEdge dsaName (MkUniversalEdge
                         (Element (PlainCmd cmd) isPlain)
                         (Element dest@(DataVal to args) isDV)
                         ) =
  let cmdStart = commandTy dsaName
      destState = genInternalValue dest
  in "\{cmd} : \{cmdStart} \{noRes} anyState (const \{destState})"

||| Generate all the universal edge commands, indented and line-separated.
genUniversalEdges : (dsaName : String) -> (ues : List UniversalEdge) -> String
genUniversalEdges dsaName ues =
  indentAndLineSep $ map (genUniversalEdge dsaName) ues

-------------------------
-- Dependent result CG --
-------------------------

||| Generate the data-type which contains the results the given dependent
||| command may return.
|||
||| @ completeDC The complete dependent command, i.e. the record containing the
|||              accumulated possible cases and destinations, as well as the
|||              command name and `from` state.
genDepResDataTy : (completeDC : DepCmdAcc) -> String
genDepResDataTy completeDC =
  resTyDecl ++ resTyConss
  where
    depResName : DepArg -> String
    -- depResName (DepsOn val) = genInternalValue val
    depResName (DepsOn val) = genTopLevelValue val

    -- the start of the result data-type declaration
    resTyDecl : String
    resTyDecl = "data \{completeDC.cmd}Res" ++ "\n" ++ indent tabWidth "= "

    -- the string form of the dependent cases
    caseNames : List1 DepRes -> List1 String
    caseNames drs = map (\dr => cleanDataConsDecl $ depResName dr.depCase) drs

    -- the constructors of the result data-type
    resTyConss : String
    resTyConss = joinBy ("\n" ++ indent tabWidth "| ") $ toList $ caseNames completeDC.cases

||| Given a list of non-plain, dependent edges, accumulate and generate the
||| dependent result data-types needed to define the corresponding commands
||| (later in the overarching process).
genDepRess :  (npdEs : List (Subset (Subset DSAEdge (Not . IsPlainEdge)) (Not . NPND)))
           -> String
genDepRess npdEs =
  joinBy "\n" $ filter (/= "") $ [depResDecls, tdResDecls, dpResDecls, tdpResDecls]
  where
    -- forget the proofs/constraints associated with the npdEs list;
    -- should be fine, since the exterior (i.e. the function you can call) is
    -- still constrained
    justTheNPDEs : List DSAEdge
    justTheNPDEs = map (Subset.fst . Subset.fst) npdEs

    -- all the dependent commands, indented and line-separated
    depResDecls : String
    depResDecls =
      case subsetFilter isDepEdge justTheNPDEs of
           [] => ""
           des@(_ :: _) => joinBy "\n" $
               map genDepResDataTy $ toList (accAllDEs $ toList1 des)

    -- all the take-dep commands, indented and line-separated
    tdResDecls : String
    tdResDecls =
      case subsetFilter isTDEdge justTheNPDEs of
           [] => ""
           tdEs@(_ :: _) => ?takedep_res_cg_not_implemented_sorry

    -- all the dep-prod commands, indented and line-separated
    dpResDecls : String
    dpResDecls =
      case subsetFilter isDPEdge justTheNPDEs of
           [] => ""
           dpEs@(_ :: _) => ?depprod_res_cg_not_implemented_sorry

    -- all the take-dep-prod commands, indented and line-separated
    tdpResDecls : String
    tdpResDecls =
      case subsetFilter isTDPEdge justTheNPDEs of
           [] => ""
           tpdEs@(_ :: _) => ?takedepprod_res_cg_not_implemented_sorry


||| Generate all the data-type declarations needed for dependent edge
||| transitions.
genDepResults :  (edges : Split IsPlainEdge allEdges)
              -> String
genDepResults edges =
  genDepRess npDepEdges
  where
    -- all the non-plain edges, paired with their proofs
    NotPlainEdges : List (Subset DSAEdge (Not . IsPlainEdge))
    NotPlainEdges = splitNawsSubset edges

    -- the split of non-plain edges, split on whether they're dependent
    npndSplit : Split NPND (reverse NotPlainEdges)
    npndSplit = split isNPND NotPlainEdges

    -- the list of non-plain, dependent edges, paired with their proofs
    npDepEdges : List (Subset (Subset DSAEdge (Not . IsPlainEdge)) (Not . NPND))
    npDepEdges = splitNawsSubset npndSplit

-------------
-- Edge CG --
-------------

||| Generate the data-types associated with the edges of the DSA.
|||
||| This includes:
|||   - plain edges
|||   - prod, take, and prod-take edges
|||   - dependent edges (and their combinations)
|||
||| @ dsaName The name of the DSA that the edges are part of.
||| @ edges The split of all the edges
genEdges :  (dsaName : String)
         -> (edges : Split IsPlainEdge allEdges)
         -> String
genEdges dsaName edges =
  joinBy "\n" $ [plainEdgeDefs, npndEdges, npDepEdges]
  where
    -- all the plain edge definitions, indented and line-separated
    plainEdgeDefs : String
    plainEdgeDefs = genPlainEdges dsaName edges.ayes edges.prfs

    -- all the non-plain edges, paired with their proofs
    NotPlainEdges : List (Subset DSAEdge (Not . IsPlainEdge))
    NotPlainEdges = splitNawsSubset edges

    -- the split of non-plain edges, split on whether they're dependent
    npndSplit : Split NPND (reverse NotPlainEdges)
    npndSplit = split isNPND NotPlainEdges

    -- all the non-plain, NON-DEPENDENT edge definitions, indented etc.
    npndEdges : String
    npndEdges =
      genNotPlainNonDepEdges dsaName $ pushIn npndSplit.ayes npndSplit.prfs

    -- all the non-plain, DEPENDENT edge definitions, indented etc.
    npDepEdges : String
    npDepEdges =
      genNonPlainDependentEdges dsaName $ pushIn npndSplit.naws npndSplit.contras

--------------
-- State CG --
--------------

-- adapted from `genDepResDataTy`
||| Generate the data-type which contains the states of the DSA
||| command may return.
|||
||| @ completeDC The complete dependent command, i.e. the record containing the
|||              accumulated possible cases and destinations, as well as the
|||              command name and `from` state.
genStates :  (dsaName : String)
          -> (states : Subset (List Value) (All IsDataVal))
          -> String
genStates dsaName states =
  stateTyDecl ++ stateTyConss
  where
    -- the start of the state data-type declaration
    stateTyDecl : String
    stateTyDecl = "data \{dsaName}State" ++ "\n" ++ indent tabWidth "= "

    -- the string form of the states
    stateNames : List Value -> List String
    stateNames =
      map (cleanDataConsDecl . genTopLevelValue)

    -- the constructors of the result data-type
    stateTyConss : String
    stateTyConss = joinBy ("\n" ++ indent tabWidth "| ") $ stateNames states.fst

-----------------------
-- Generating Idris2 --
-----------------------

||| Convert the given `DSA` to Idris2 source code.
export
toIdris2 : DSAv2 -> String
toIdris2 (MkDSAv2 dsaName states edges universalEdges) =
  let states = genStates dsaName states
      depResults = genDepResults edges
      cmdDecl = genCmdDecl dsaName
      edgeCmds = genEdges dsaName edges
      univEdgeCmds = genUniversalEdges dsaName universalEdges
      thePureCmd = pureCmd dsaName
      theBindCmd = bindCmd dsaName
  in joinBy "\n\n" $ filter (/= "") $
     [ states
     , depResults
     , cmdDecl
     , edgeCmds
     , univEdgeCmds
     , thePureCmd
     , theBindCmd
     ]


--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------

-------------------------
-- Basic data cons gen --
-------------------------

||| "Test : ATMCmd"
testGenDataCons1 : String
testGenDataCons1 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" Nothing) ItIsDataVal)

||| "Test : sn -> ATMCmd"
testGenDataCons2 : String
testGenDataCons2 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: []))) ItIsDataVal)

||| "Test : sn -> (sn + 1) -> ATMCmd"
testGenDataCons3 : String
testGenDataCons3 =
  genDataConsDecl "ATMCmd" (Element (DataVal "Test" (Just ((IdrName "sn") ::: [AddExpr (IdrName "sn") (LitVal 1)]))) ItIsDataVal)


------------
-- UE gen --
------------

||| "UETest : ATMCmd () anyState (const Ready)"
testGenUE1 : String
testGenUE1 =
  let cmd : Subset DSALabel IsPlainCmd
          = Element (PlainCmd "UETest") ItIsPlain
      dest : Subset Value IsDataVal
           = Element (DataVal "Ready" Nothing) ItIsDataVal
  in genUniversalEdge "ATM" (MkUniversalEdge cmd dest)

||| "UETest : ATMCmd () anyState (const (Ready a b))"
testGenUE2 : String
testGenUE2 =
  let cmd : Subset DSALabel IsPlainCmd
          = Element (PlainCmd "UETest") ItIsPlain
      dest : Subset Value IsDataVal
           = Element (DataVal "Ready" (Just $ (IdrName "a") ::: [IdrName "b"])) ItIsDataVal
  in genUniversalEdge "ATM" (MkUniversalEdge cmd dest)

--------------------
-- Plain edge gen --
--------------------

||| "EjectCard : ATMCmd () Session (const Ready)
testGenPlainEdge1 : String
testGenPlainEdge1 =
  genPlainEdge "ATM" edge
  where
      cmd : DSALabel
      cmd = PlainCmd "EjectCard"

      from : Subset Value IsDataVal
      from = Element (DataVal "Session" Nothing) ItIsDataVal

      to : Subset Value IsDataVal
      to = Element (DataVal "Ready" Nothing) ItIsDataVal

      edge : Subset DSAEdge IsPlainEdge
      edge = Element (MkDSAEdge cmd from to) EdgeIsPlain

||| "EjectCard : ATMCmd () (Session (c, d)) (const (Ready a (b + 2)))
testGenPlainEdge2 : String
testGenPlainEdge2 =
  genPlainEdge "ATM" edge
  where
      cmd : DSALabel
      cmd = PlainCmd "EjectCard"

      fromArgs : Maybe $ List1 Value
      fromArgs = Just $ (Tuple (IdrName "c") (IdrName "d")) ::: []

      from : Subset Value IsDataVal
      from = Element (DataVal "Session" fromArgs) ItIsDataVal

      toArgs : Maybe $ List1 Value
      toArgs = Just $ (IdrName "a") ::: [AddExpr (IdrName "b") (LitVal 2)]

      to : Subset Value IsDataVal
      to = Element (DataVal "Ready" toArgs) ItIsDataVal

      edge : Subset DSAEdge IsPlainEdge
      edge = Element (MkDSAEdge cmd from to) EdgeIsPlain

-------------------
-- Take-edge gen --
-------------------

||| "CheckPIN : PIN -> ATMCmd () CardInserted (const Session)"
testGenTakeEdge1 : String
testGenTakeEdge1 =
  genTakeEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    arg : TakeArg
    arg = Takes (IdrName "PIN")

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (TakeCmd cmd arg) from to

||| "CheckPIN : (PIN, (1 + n)) -> ATMCmd () (CardInserted (c, d)) (const (Session a (b + 2)))"
testGenTakeEdge2 : String
testGenTakeEdge2 =
  genTakeEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    arg : TakeArg
    arg = Takes (Tuple (IdrName "PIN") (AddExpr (LitVal 1) (IdrName "n")))

    fromArgs : Maybe $ List1 Value
    fromArgs = Just $ (Tuple (IdrName "c") (IdrName "d")) ::: []

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" fromArgs) ItIsDataVal

    toArgs : Maybe $ List1 Value
    toArgs = Just $ (IdrName "a") ::: [AddExpr (IdrName "b") (LitVal 2)]

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" toArgs) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (TakeCmd cmd arg) from to

-------------------
-- Prod-edge gen --
-------------------

||| "CheckPIN : ATMCmd (PINCheck) CardInserted (const Session)"
testGenProdEdge1 : String
testGenProdEdge1 =
  genProdEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    res : ProdArg
    res = Produce (DataVal "PINCheck" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (ProdCmd cmd res) from to

||| "CheckPIN : ATMCmd ((PINCheck pin), sTok) (CardInserted (c, (1 + d))) (const (Session sTok))"
testGenProdEdge2 : String
testGenProdEdge2 =
  genProdEdge "ATM" edge
  where
    cmd : String
    cmd = "CheckPIN"

    pcArg : Maybe $ List1 Value
    pcArg = Just $ (IdrName "pin") ::: []

    res : ProdArg
    res = Produce (Tuple (DataVal "PINCheck" pcArg) (IdrName "sTok"))

    fromArgs : Maybe $ List1 Value
    fromArgs = Just $
               (Tuple (IdrName "c") (AddExpr (LitVal 1) (IdrName "d"))) ::: []

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" fromArgs) ItIsDataVal

    toArgs : Maybe $ List1 Value
    toArgs = Just $ (IdrName "sTok") ::: []

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" toArgs) ItIsDataVal

    edge : DSAEdge
    edge = MkDSAEdge (ProdCmd cmd res) from to

------------------------
-- Take-prod-edge gen --
------------------------

||| "CheckPIN : (PIN) -> ATMCmd (PINCheck) (CardInserted) (const (Session))"
testGenTPEdge1 : String
testGenTPEdge1 =
  genTPEdge "ATM" tpEdge
  where
    cmd : String
    cmd = "CheckPIN"

    takes : TakeArg
    takes = Takes (DataVal "PIN" Nothing)

    returns : ProdArg
    returns = Produce (DataVal "PINCheck" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "CardInserted" Nothing) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Session" Nothing) ItIsDataVal

    tpEdge : DSAEdge
    tpEdge = MkDSAEdge (TPCmd cmd takes returns) from to

||| "Send : (SeqNo sn) -> ARQCmd ((SeqNo sn), (csn + 1)) (Ready sn csn) (const (Waiting sn (csn + 1)))"
testGenTPEdge2 : String
testGenTPEdge2 =
  genTPEdge "ARQ" tpEdge
  where
    cmd : String
    cmd = "Send"

    -- sequence number
    sn : Value
    sn = IdrName "sn"

    seqNo : Value
    seqNo = DataVal "SeqNo" (Just (sn ::: []))

    takes : TakeArg
    takes = Takes seqNo

    -- current sequence number
    csn : Value
    csn = IdrName "csn"

    one : Value
    one = LitVal 1

    returns : ProdArg
    returns = Produce (Tuple seqNo (AddExpr csn one))

    from : Subset Value IsDataVal
    from = Element (DataVal "Ready" (Just (sn ::: [csn]))) ItIsDataVal

    to : Subset Value IsDataVal
    to = Element (DataVal "Waiting" (Just (sn ::: [AddExpr csn one]))) ItIsDataVal

    tpEdge : DSAEdge
    tpEdge = MkDSAEdge (TPCmd cmd takes returns) from to

---------------------------
-- Dep-edge accumulation --
---------------------------

accDEs1 : DepCmdAcc
accDEs1 = accDEs $ singleton de1
  where
    da1 : DepArg
    da1 = DepsOn (DataVal "Res1" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "FromState" Nothing) ItIsDataVal

    to1 : Subset Value IsDataVal
    to1 = Element (DataVal "ToState1" Nothing) ItIsDataVal

    de1 : Subset DSAEdge IsDepEdge
    de1 = Element (MkDSAEdge (DepCmd "ADepCmd" da1) from to1) ItIsDepEdge

||| "{ DepCmdAcc \"ADepCmd\"
|||              Element (DataVal FromState) _
|||              [{ DepRes (DepsOn (DataVal Res1)) Element (DataVal ToState1) _ }]
|||  }"
testAccDEs1 : String
testAccDEs1 = show accDEs1

accDEs2 : DepCmdAcc
accDEs2 = accDEs $ de1 ::: [de2]
  where
    da1 : DepArg
    da1 = DepsOn (DataVal "Res1" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "FromState" Nothing) ItIsDataVal

    to1 : Subset Value IsDataVal
    to1 = Element (DataVal "ToState1" Nothing) ItIsDataVal

    de1 : Subset DSAEdge IsDepEdge
    de1 = Element (MkDSAEdge (DepCmd "ADepCmd" da1) from to1) ItIsDepEdge

    da2 : DepArg
    da2 = DepsOn (DataVal "Res2" Nothing)

    to2 : Subset Value IsDataVal
    to2 = Element (DataVal "ToState2" Nothing) ItIsDataVal

    de2 : Subset DSAEdge IsDepEdge
    de2 = Element (MkDSAEdge (DepCmd "ADepCmd" da2) from to2) ItIsDepEdge

||| "{ DepCmdAcc \"ADepCmd\"
|||              Element (DataVal FromState) _
|||              [ { DepRes (DepsOn (DataVal Res2)) Element (DataVal ToState2) _ }
|||              , { DepRes (DepsOn (DataVal Res1)) Element (DataVal ToState1) _ }
|||              ]
|||  }"
testAccDEs2 : String
testAccDEs2 = show accDEs2

accDEs3 : DepCmdAcc
accDEs3 = accDEs $ de1 ::: [de2, de3]
  where
    da1 : DepArg
    da1 = DepsOn (DataVal "Res1" Nothing)

    from : Subset Value IsDataVal
    from = Element (DataVal "FromState" Nothing) ItIsDataVal

    to1 : Subset Value IsDataVal
    to1 = Element (DataVal "ToState1" Nothing) ItIsDataVal

    de1 : Subset DSAEdge IsDepEdge
    de1 = Element (MkDSAEdge (DepCmd "ADepCmd" da1) from to1) ItIsDepEdge

    da2 : DepArg
    da2 = DepsOn (DataVal "Res2" (Just $ (DataVal "Arg2_1" Nothing) ::: []))

    to2 : Subset Value IsDataVal
    to2 = Element (DataVal "ToState2" Nothing) ItIsDataVal

    de2 : Subset DSAEdge IsDepEdge
    de2 = Element (MkDSAEdge (DepCmd "ADepCmd" da2) from to2) ItIsDepEdge

    da3Args : List1 Value
    da3Args = (DataVal "Arg3_1" Nothing) ::: [Tuple (DataVal "Arg3_1" Nothing) (DataVal "Arg3_2" Nothing)]

    da3 : DepArg
    da3 = DepsOn (DataVal "Res3" (Just da3Args))

    to3 : Subset Value IsDataVal
    to3 = Element (DataVal "ToState3" (Just $ (DataVal "ts3_1" Nothing) ::: [])) ItIsDataVal

    de3 : Subset DSAEdge IsDepEdge
    de3 = Element (MkDSAEdge (DepCmd "ADepCmd" da3) from to3) ItIsDepEdge

||| "{ DepCmdAcc \"ADepCmd\"
|||             Element (DataVal FromState) _
|||             [ { DepRes (DepsOn (DataVal Res3 (DataVal Arg3_1) (Tuple (DataVal Arg3_1) (DataVal Arg3_2))) Element (DataVal ToState3 (DataVal ts3_1) _ }
|||             , { DepRes (DepsOn (DataVal Res2 (DataVal Arg2_1)) Element (DataVal ToState2) _ }
|||             , { DepRes (DepsOn (DataVal Res1)) Element (DataVal ToState1) _ }
|||             ]
|||  }"
testAccDEs3 : String
testAccDEs3 = show accDEs3

-------------------------
-- Dep-edge result gen --
-------------------------

||| "data ADepCmdRes
|||    = Res1"
testGenDepResDataTy1 : String
testGenDepResDataTy1 = genDepResDataTy accDEs1

||| "data ADepCmdRes
|||    = Res2
|||    | Res1"
testGenDepResDataTy2 : String
testGenDepResDataTy2 = genDepResDataTy accDEs2

||| "data ADepCmdRes
|||    = Res3 (Arg3_1) ((Arg3_1), (Arg3_2))
|||    | Res2 (Arg2_1)
|||    | Res1"
testGenDepResDataTy3 : String
testGenDepResDataTy3 = genDepResDataTy accDEs3

--------------------------
-- Dep-edge case-fn gen --
--------------------------

||| "(\\case (Res1) => (ToState1))"
testGenDepCmdCaseExpr1 : String
testGenDepCmdCaseExpr1 = genDepCmdCaseExpr accDEs1

||| "(\\case (Res2) => (ToState2); (Res1) => (ToState1))"
testGenDepCmdCaseExpr2 : String
testGenDepCmdCaseExpr2 = genDepCmdCaseExpr accDEs2

||| "(\\case (Res3 (Arg3_1) ((Arg3_1), (Arg3_2))) => (ToState3 (ts3_1)); (Res2 (Arg2_1)) => (ToState2); (Res1) => (ToState1))"
testGenDepCmdCaseExpr3 : String
testGenDepCmdCaseExpr3 = genDepCmdCaseExpr accDEs3

--------------------------
-- Dep-edge command gen --
--------------------------

||| "ADepCmd : TestDSACmd (ADepCmdRes) (FromState) (\\case (Res1) => (ToState1))"
testGenDepCmdBody1 : String
testGenDepCmdBody1 = genDepCmdBody "TestDSA" accDEs1

||| "ADepCmd : TestDSACmd (ADepCmdRes) (FromState) (\\case (Res2) => (ToState2); (Res1) => (ToState1))"
testGenDepCmdBody2 : String
testGenDepCmdBody2 = genDepCmdBody "TestDSA" accDEs2

||| "ADepCmd : TestDSACmd (ADepCmdRes) (FromState) (\\case (Res3 (Arg3_1) ((Arg3_1), (Arg3_2))) => (ToState3 (ts3_1)); (Res2 (Arg2_1)) => (ToState2); (Res1) => (ToState1))"
testGenDepCmdBody3 : String
testGenDepCmdBody3 = genDepCmdBody "TestDSA" accDEs3

---------------
-- State gen --
---------------

states1 : Subset (List Value) (All IsDataVal)
states1 = Element [ DataVal "State1" Nothing
                  , DataVal "State2" Nothing
                  ]
                  %search

||| "data TestDSAState
|||    = State1
|||    | State2"
testGenStates1 : String
testGenStates1 = genStates "TestDSA" states1

states2 : Subset (List Value) (All IsDataVal)
states2 = Element [ DataVal "State1" Nothing
                  , DataVal "State2" (Just $ singleton (DataVal "Nat" Nothing))
                  ]
                  %search

||| "data TestDSAState
|||    = State1
|||    | State2 (Nat)"
testGenStates2 : String
testGenStates2 = genStates "TestDSA" states2

states3 : Subset (List Value) (All IsDataVal)
states3 = Element [ DataVal "State1" Nothing
                  , s2
                  , s3
                  ]
                  %search
  where
    s2 : Value
    s2 = DataVal "State2" (Just $ singleton (DataVal "Nat" Nothing))

    seqNoTy : Value
    seqNoTy = DataVal "SeqNo" (Just $ singleton (IdrName "sn"))

    s3 : Value
    s3 = DataVal "State3" (Just $ (Tuple (DataVal "Type" Nothing) seqNoTy) ::: [DataVal "Nat" Nothing])

||| "data TestDSAState
|||    = State1
|||    | State2 Nat
|||    | State3 (Type, (SeqNo sn)) Nat"
testGenStates3 : String
testGenStates3 = genStates "TestDSA" states3

