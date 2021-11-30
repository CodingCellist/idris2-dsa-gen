module DSAGen.DOTDSA

import Graphics.DOT

import DSAGen.DSL

import Data.List
import Data.List1
import Data.Vect
import Data.String
import Data.SnocList

%default total

-- TODO: Should possibly be an interface in `dot-parse`?
export
interface DOTAble a where
  toDOT : a -> DOT

-- TODO: prove that string is non-empty? and/or that it's a valid Idris name?
||| Labels are lists of at least one string.
export
data DDLabel : Type where
  MkDDLabel : (vals : Vect (S k) String) -> DDLabel

export
DOTAble DDLabel where
  toDOT (MkDDLabel vals) =
    -- each of the values must be comma-separated
    let valStr = foldr1 (++) $ intersperse ", " vals
    in Assign [(NameID "label"), (StringID valStr)]

-- FIXME: is this the right name for this?
export
DDIdentifier : Type
DDIdentifier = String

export
DOTAble DDIdentifier where
  -- i never contains spaces (FIXME: assumption), so no need to use `StringID`
  toDOT i = NameID i

||| A valid Idris name is at least one aplhabetical character followed by a
||| number of alphanumerical or underscore characters.
isValidIdrName : List Char -> Bool
isValidIdrName [] = False
isValidIdrName (c :: cs) = isAlpha c && all (\c => isAlphaNum c || c == '_') cs

||| A string describes a dependent edge iff it contains a valid idris name,
||| followed by a '(', followed by a valid idris name, followed by a ')'.
isDepEdge : String -> Bool
isDepEdge s =
  -- FIXME: fix words' totality
  -- let cs = unpack $ concat (map trim (assert_total $ words s))  
  let cs = unpack s
  in case span (/= '(') cs of 
         ([], _) => False
         (_ , []) => False
         (tName, (_ :: cs')) =>       -- ignore the '(' which is included by `span`
             case Lin <>< cs' of
                  resName :< ')' =>   -- check that we close the parenthesis
                      isValidIdrName tName && isValidIdrName (toList resName)
                  _ => False

||| Checks that the values given from `toLabel` are valid DSA values. Each
||| value is accepted iff it is a valid Idris name or it is a dependent edge.
labelValsOK : (vals : List String) -> {auto 0 ok : NonEmpty vals} -> Bool
labelValsOK [] impossible
labelValsOK vals = all (\v => (isValidIdrName . unpack) v || isDepEdge v) vals

||| Remove the leading and trailing '"' of the `str` contained in a DOT's `StringID`.
cleanStringID : String -> String
cleanStringID id_ = substr 1 ((length id_) `minus` 2) id_
                             -- substr is 0-based  ^

||| Convert the given DOT to a `Label`. Some DOT is a `Label` iff it is an
||| assignment from the name "label" to a StringID consisting of at least one
||| valid transition (see `labelValsOK` for more details on what that means).
export
toDDLabel : DOT -> Maybe DDLabel
toDDLabel (Assign [NameID "label", StringID rawVals]) =
  case split (== ',') (cleanStringID rawVals) of
       (head ::: tail) =>
               let head' = trim head
                   tail' = map trim tail
               in if labelValsOK (head' :: tail')
                     then Just $ MkDDLabel (fromList (head' :: tail'))
                     else Nothing

toDDLabel _ = Nothing


||| An edge in a DOT model of a DSA.
export
data DDEdge : Type where
  ||| The edge must have a `from` node and a `to` node, as well as be labelled
  ||| (in order for the transition it describes to have a name).
  MkDDEdge :  (from  : DDIdentifier)
           -> (to    : DDIdentifier)
           -> (label : DDLabel)
           -> DDEdge

export
DOTAble DDEdge where
  -- "from" is the id of a node;
  -- same with "to", but it is part of the RHS of an edge statement and we only
  -- allow directed edges in DOT diagrams of DSAs;
  -- "l" is the edge's label's values, which need to be wrapped in an `AttrList`
  -- and an `AList` to conform to the DOT grammar.
  toDOT (MkDDEdge from to label) =
    EdgeStmt (NodeID (NameID from) Nothing)
             (EdgeRHS [DiGrEdgeOp, (NodeID (NameID to) Nothing)])
             (Just $ AttrList [AList [toDOT label]])

||| Returns the given string in a `Just` iff it is a valid Idris name.
toIdentifier : (s : String) -> Maybe DDIdentifier
toIdentifier s = toMaybe (isValidIdrName $ unpack s) s

||| Convert the given DOT to an identifier. Some DOT is an identifier iff it
||| is either a NameID or a StringID, and if that ID is a valid Idris name.
export
dotToIdentifier : DOT -> Maybe DDIdentifier
dotToIdentifier (NameID   n) = toIdentifier n
dotToIdentifier (StringID s) = toIdentifier (cleanStringID s)
dotToIdentifier _ = Nothing

||| Convert the given DOT to a `LDDEdge`. Some DOT is an edge in a DSA iff it
||| goes from a `NodeID` to a `NodeID` using a directed edge, with a single
||| attribute detailing the labelling of the edge.
export
toDDEdge : DOT -> Maybe DDEdge
toDDEdge (EdgeStmt (NodeID f _) (EdgeRHS [DiGrEdgeOp, (NodeID t _)]) (Just (AttrList [AList [attr]]))) =
  do from <- dotToIdentifier f
     to <- dotToIdentifier t
     ddLabel <- toDDLabel attr
     pure (MkDDEdge from to ddLabel)

toDDEdge _ = Nothing

||| Convert a DOT statement to a part of a DOTDSA. The statement is valid in the
||| DSA iff it is a `Stmt` containing an `EdgeStmt`.
export
handleStmt : DOT -> Maybe DDEdge
handleStmt (Stmt (EdgeStmt f rhs attrList)) = toDDEdge (EdgeStmt f rhs attrList)
handleStmt _ = Nothing

||| A slightly more restricted version of DOT for easier conversion to a DSA.
export
data DOTDSA : Type where
    DSAGraph :  (name  : DDIdentifier)
             -> (edges : List DDEdge)
             -> {auto 0 ok : NonEmpty edges}
             -> DOTDSA

export
DOTAble DOTDSA where
  -- A DOTDSA is non-strict, directed graph;
  -- which _does_ have a name;
  -- and whose statements are a list of edge-statements, each of which needs to
  -- be wrapped in a `Stmt` to conform to the DOT grammar.
  toDOT (DSAGraph name edges) =
    Graph False DiGraph
          (Just (NameID name))
          (StmtList (Stmt <$> map toDOT edges))

||| Convert the given `DOT` to the subset `DOTDSA`, which describes a DSA.
export
toDOTDSA : DOT -> Maybe DOTDSA
toDOTDSA (Graph False DiGraph (Just n) (StmtList stmts)) =
  do name <- dotToIdentifier n
     (e :: es) <- traverse handleStmt stmts
        | [] => Nothing
     pure (DSAGraph name (e :: es))

toDOTDSA _ = Nothing


--------------------
-- DOTDSA ==> DSA --
--------------------

||| Given a `DDEdge` and a list of existing `State`s, if the `State`s resulting
||| from the `DDEdge` (the `DDEdge`'s `from` and `to`) are not already in the
||| list of existing `State`s, convert them to `State`s and add them to the
||| accumulator.
addState : (dde : DDEdge) -> (acc : List State) -> List State
addState (MkDDEdge from to _) acc =
  let fState = newState from
      tState = newState to
      acc' = addIfMissing fState acc
  in addIfMissing tState acc'
  where
    addIfMissing : (s : State) -> (acc : List State) -> List State
    addIfMissing s acc = if elem s acc then acc else s :: acc

||| Add all the unique `State`s resulting from `ddes` to the accumulator, if
||| they are not already in the accumulator (see also `addState`).
|||
||| @ ddes the list of `DDEdge`s to convert to `State`s and potentially add
||| @ acc  the accumulator of existing `State`s to check against for uniqueness
genStates : (ddes : List DDEdge) -> (acc : List State) -> List State
genStates [] acc = acc
genStates (dde :: ddes) acc =
  let acc' = addState dde acc
  in genStates ddes acc'

||| Given a `DDEdge` and a list of existing `Edge`s, if the `Edge` resulting
||| from the `DDEdge` is not already in the list of existing `Edge`s, convert it
||| to an `Edge` and add the resulting `Edge` to the accumulator.
addEdge : (dde : DDEdge) -> (acc : List Edge) -> List Edge
addEdge (MkDDEdge from to (MkDDLabel vals)) acc =
  let edges = map (toEdge from to) vals
  in addEdge' (toList edges) acc
  where
    addIfMissing : (e : Edge) -> (acc : List Edge) -> List Edge
    addIfMissing e acc = if elem e acc then acc else e :: acc

    addEdge' : (es : List Edge) -> (acc : List Edge) -> List Edge
    addEdge' [] acc = acc
    addEdge' (e :: es) acc =
      let acc' = addIfMissing e acc
      in addEdge' es acc'

    ||| Given a value representing a dependent action, split off the name of the
    ||| action and its dependent result.
    splitDepAction : (val : String) -> (String, String)
    splitDepAction val =
      let -- strip the parentheses from the value
          (actName, rest) = span (/= '(') val
          resName = substr 1 ((length rest) `minus` 2) rest
      in (actName, resName)

    ||| Given the 'from', the 'to', and a 'label' from a `DDEdge`, decide
    ||| whether the 'label' represents a dependent edge or a regular edge and
    ||| convert it as appropriate.
    toEdge : (f : String) -> (t : String) -> (val : String) -> Edge
    toEdge f t val =
      let tState = newState t
          fState = newState f
      in if isDepEdge val
            then let (actName, resName) = splitDepAction val
                     actLbl = MkLabel actName
                     depRes = MkDepRes resName tState
                 in DepAction actLbl fState [depRes]
            else RegAction (MkLabel val) fState tState

||| Add all the unique `Edge`s resulting from `ddes` to the accumulator, if
||| they are not already in the accumulator (see also `addEdge`).
|||
||| @ ddes the list of `DDEdge`s to convert to `Edge`s and potentially add
||| @ acc  the accumulator of existing `Edge`s to check against for uniqueness
genEdges : (ddes : List DDEdge) -> (acc : List Edge) -> List Edge
genEdges [] acc = acc
genEdges (dde :: ddes) acc =
  let acc' = addEdge dde acc
  in genEdges ddes acc'

||| Given a list of `Edge`s and an accumulator for dependent edges, separate
||| out the dependent edges from the first list and merge the `DepRes`'s of
||| edges starting at the same point.
combineDepEdges : (es : List Edge) -> (depAcc : List Edge) -> List Edge
combineDepEdges es depAcc =
  let (deps, regs) = partition isDepAction es
  in regs ++ mergeDepEdges' deps
  where
    isDepAction : Edge -> Bool
    isDepAction (RegAction _ _ _) = False
    isDepAction (DepAction _ _ _) = True

    sameName : Edge -> Edge -> Bool
    sameName e1 e2 = (name e1) == (name e2)

    ||| Given a list of `Edge`s originating from the same point as `onto`,
    ||| extract their dependent results and add them to the dependent results of
    ||| `onto`.
    combineDepRes : (es : List Edge) -> (onto : Edge) -> Edge
    combineDepRes [] onto = onto
    combineDepRes es onto =
      let nm = name onto
          fromState = from onto
          dt = depTo onto
          depTos = extractDepStates es
          combined = foldr (++) dt depTos
      in DepAction (name onto) (from onto) combined

    ||| Take the first dependent edge, find all its partners and merge them,
    ||| then handle the rest of the list if there is anything left.
    mergeDepEdges' : (deps : List Edge) -> List Edge
    mergeDepEdges' [] = []
    mergeDepEdges' (de :: des) =
      let (toMerge, rest) = partition (sameName de) des
      in combineDepRes toMerge de :: mergeDepEdges' (assert_smaller des rest)
                                                    -- ^ FIXME ?

export
DSADesc DOTDSA where
  toDSA (DSAGraph name ddEdges) =   -- TODO: name is currently discarded
    let dsaStates = genStates ddEdges []
        rawEdges  = genEdges  ddEdges []
        dsaEdges  = combineDepEdges rawEdges []
    in MkDSA dsaStates dsaEdges

