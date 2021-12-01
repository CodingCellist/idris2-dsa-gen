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

addState2 : (dde : DDEdge) -> (acc : List State) -> List State
addState2 (MkDDEdge from to _) acc =
  let fState = newState from
      tState = newState to
      acc' = addIfMissing fState acc
  in addIfMissing tState acc'
  where
    addIfMissing : (s : State) -> (acc : List State) -> List State
    addIfMissing s acc = if elem s acc then acc else s :: acc

genStates2 : (ddes : List DDEdge) -> (acc : List State) -> List State
genStates2 [] acc = acc
genStates2 (dde :: ddes) acc =
  let acc' = addState2 dde acc
  in genStates2 ddes acc'

||| A representation of a DDEdge with only one (1) destination.
data SingleDDEdge : Type where
  MkSDDE :  (from : DDIdentifier)
         -> (to   : DDIdentifier)
         -> (name : Vect 1 String)
         -> SingleDDEdge

||| Partition the given list of `DDEdge`s into two lists: one containing the
||| edges describing a dependent transition, and another containing the edges
||| describing a regular transition.
|||
||| N.B.: Since multiple edges can be defined in one `DDEdge`'s "label", the
||| resulting lists may have a combined length greater than the length of the
||| input list.
partitionDDEdges : (ddes : List DDEdge) -> (List SingleDDEdge, List SingleDDEdge)
-- partitionDDEdges : (ddes : List DDEdge) -> (List DDEdge, List DDEdge)
partitionDDEdges [] = ([], [])
partitionDDEdges (dde :: ddes) =
  let (deps     , regs    ) = splitEdge dde
      (moreDeps , moreRegs) = unzipWith splitEdge ddes
  -- combine all the lists of lists into one big list (for deps and regs respectively)
  in ( deps ++ foldr (++) [] moreDeps
     , regs ++ foldr (++) [] moreRegs )
  where
    ||| Split the label's values into dependent and regular values.
    splitLabelVals :  (vals : Vect (S k) String)
                   -> (acc  : (List String, List String))
                   -> (List String, List String)
    splitLabelVals (v :: []) (ds, rs) =
      if isDepEdge v
         then (v :: ds , rs     )
         else (ds      , v :: rs)
    splitLabelVals (v :: vs@(_ :: _)) (ds, rs) =
      if isDepEdge v
         then let acc' = (v :: ds , rs     ) in splitLabelVals vs acc'
         else let acc' = (ds      , v :: rs) in splitLabelVals vs acc'

    ||| Split a single DDEdge into potentially multiple edges: dependent edges
    ||| and regular edges.
    splitEdge : DDEdge -> (List SingleDDEdge, List SingleDDEdge)
    -- splitEdge : DDEdge -> (List DDEdge, List DDEdge)
    splitEdge (MkDDEdge from to (MkDDLabel vals)) =
      let (depVals, regVals) = splitLabelVals vals ([], [])
          partialDDEdge = \s => MkSDDE from to [s]
      in (map partialDDEdge depVals, map partialDDEdge regVals)

||| Convert a DDEdge describing a single regular edge to a `RegEdge`.
toRegEdge : (regDDE : SingleDDEdge) -> RegEdge
toRegEdge (MkSDDE from to (name :: [])) =
  let nameLbl   = MkLabel name
      fromState = newState from
      toState   = newState to
  in MkRegEdge nameLbl fromState toState

||| Convert a DDEdge describing a single dependent edge to a `DepEdge`.
toDepEdge : (depDDE : SingleDDEdge) -> DepEdge
toDepEdge (MkSDDE from to (depLbl :: [])) =
  let (name, depRes) = splitDepLabel depLbl
      fromState = newState from
  in MkDepEdge name fromState [depRes]
  where
    ||| Split the given label into the name of the transition, and the name of
    ||| the result it depends on.
    splitDepLabel : (lbl : String) -> (Label, DepRes)
    splitDepLabel lbl =
      let (name, rest) = span (/= '(') lbl
          resName = substr 1 ((length rest) `minus` 2) rest
          toState = newState to
      in (MkLabel name, MkDepRes resName toState)

||| Returns `True` iff the given `DepEdge`s have the same name.
deHaveSameName : DepEdge -> DepEdge -> Bool
deHaveSameName (MkDepEdge n1 _ _) (MkDepEdge n2 _ _) = n1 == n2

||| Combine the given dependent edges' `DepRes`'s into a single `DepEdge` with
||| all the results, using `theDE` as a starting point.
combineDepEdgesUsing : (theDE : DepEdge) -> (des : List DepEdge) -> DepEdge
combineDepEdgesUsing (MkDepEdge name from dt) des =
  let otherDRs = map depTo des
      allDRs = dt ++ foldr (++) [] otherDRs
  in MkDepEdge name from allDRs

||| Combine the given list of unprocessed dependent edges into a list of
||| `DepEdge`s s.t. all edges with the same name have had their `DepRes`'s
||| combined.
combineDepEdges : (rawDEs : List DepEdge) -> List DepEdge
combineDepEdges [] = []
combineDepEdges (rde :: rdes) =
  let (toCombine, rest) = partition (deHaveSameName rde) rdes
      -- acc' = (combineDepEdgesUsing rde toCombine) :: acc
      combined = combineDepEdgesUsing rde toCombine
  in combined :: combineDepEdges (assert_smaller rdes rest)

export
DSADesc DOTDSA where
  toDSA (DSAGraph name ddEdges) =
    let dsaStates = genStates2 ddEdges []
        (rawDEs, rawREs) = partitionDDEdges ddEdges
        regEdges = map toRegEdge rawREs
        depEdges = combineDepEdges $ map toDepEdge rawDEs
    in MkDSA name dsaStates regEdges depEdges

