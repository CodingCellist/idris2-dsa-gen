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

