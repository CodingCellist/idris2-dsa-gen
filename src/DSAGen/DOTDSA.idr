module DSAGen.DOTDSA

import Graphics.DOT

import Data.List
import Data.List1
import Data.Vect
import Data.String

%default total

-- TODO: Should possibly be an interface in `dot-parse`?
export
interface DOTAble a where
  toDOT : a -> DOT

-- FIXME: OLD LABEL IMPLEMENTATION --
-- TODO: prove that there was a "label" keyword on creation?
-- ||| Labels are just strings, but we only create them from a "label" keyword
-- Label : Type
-- Label = String
-- 
-- DOTAble Label where
--   toDOT l = Assign [(NameID "label"), (StringID l)]

-- TODO: prove that string is non-empty? and/or that it's a valid Idris name?
||| Labels are lists of at least one string.
export
data Label : Type where
  MkLabel : (vals : Vect (S k) String) -> Label

export
DOTAble Label where
  toDOT (MkLabel vals) =
    -- each of the values must be comma-separated
    let valStr = foldr1 (++) $ intersperse ", " vals
    in Assign [(NameID "label"), (StringID valStr)]

-- FIXME: what's the right name?
Identifier : Type
Identifier = String

DOTAble Identifier where
  -- i never contains spaces (FIXME: assumption), so no need to use `StringID`
  toDOT i = NameID i

||| A valid Idris name is at least one aplhabetical character followed by a
||| number of alphanumerical or underscore characters.
export
isValidIdrName : List Char -> Bool
isValidIdrName [] = False
isValidIdrName (c :: cs) = isAlpha c && all (\c => isAlphaNum c || c == '_') cs

-- ||| If the DOT was `label="<value>"`, then we can extract the `Label`.
-- toLabel : (id_ : String) -> Maybe Label
-- toLabel id_ = toMaybe (isValidIdrName $ unpack id_) id_

||| Returns the given string in a `Just` iff it is a valid Idris name.
toIdentifier : (s : String) -> Maybe Identifier
toIdentifier s = toMaybe (isValidIdrName $ unpack s) s

||| A dependent transition consists of the name of the transition, and the
||| accepted dependent result which allows the transition to happen. A regular
||| transition has no dependent result.
data Transition : Type where
  MkTransition :  (tName   : Identifier)
               -> (resName : Maybe Identifier)
               -> Transition

DOTAble Transition where
  -- TODO: make these `Label`s
  toDOT (MkTransition tName Nothing) =
    Assign [(NameID "label"), (StringID tName)]
  toDOT (MkTransition tName (Just rn)) = ?transToDOT_rhs_2

||| Return a `Transition` iff the input `id_` has the form "<tName>(<resName>)",
||| for example:
||| "CheckPIN(Incorrect)"
toDepTrans : (id_ : String) -> Maybe Transition
toDepTrans id_ =
   let cs = unpack id_
   in case span ((==) '(') cs of 
           ([], _) => Nothing
           (_ , []) => Nothing
           (tName, (_ :: cs')) =>
             case span ((==) ')') cs' of
                  ([], _) => Nothing
                  (resName, _) =>
                       if isValidIdrName tName && isValidIdrName resName
                          then Just $ MkTransition (pack tName) (Just $ pack resName)
                          else Nothing

||| Return a `Transition` iff the input `id_` is a valid Idris name, for
||| example:
||| "GetPIN"
toRegTrans : (id_ : String) -> Maybe Transition
toRegTrans id_ =
  if (isValidIdrName . unpack) id_
     then Just $ MkTransition id_ Nothing
     else Nothing

||| Return a `Transition` iff the input `id_` is a valid Idris name.
toTransition : (id_ : String) -> Maybe Transition
toTransition id_ =
  case toDepTrans id_ of
       Nothing => toRegTrans id_
       (Just dt) => Just dt

||| A "label"'s associated value is valid iff it is a `NameID` or a `StringID`.
isValidLabelVal : DOT -> Bool
isValidLabelVal (NameID _) = True
isValidLabelVal (StringID _) = True
isValidLabelVal _ = False

||| Attempt to convert a "label"'s value to a list of `Transition`s. Only works
||| if the list is comma-separated.
tryMultiTrans : DOT -> Maybe (List Transition)
tryMultiTrans (StringID s) =
  case split (== ',') s of
       (head ::: []) => Nothing
       (head ::: (x :: xs)) =>
            do let head' = trim head
               let rest  = map trim (x :: xs)
               t <- toTransition head'
               ts <- traverse toTransition rest
               pure (t :: ts)

tryMultiTrans _ = Nothing

tryDepTrans : DOT -> Maybe Transition
tryDepTrans (StringID id_) = toDepTrans id_
tryDepTrans _              = Nothing

tryRegTrans : DOT -> Maybe Transition
tryRegTrans (NameID id_)   = toRegTrans id_
tryRegTrans (StringID id_) = toRegTrans id_
tryRegTrans _              = Nothing

||| Assignment in DOT is a valid DSA property iff it assigns a "label" AND the
||| value of the label is either 1) a dependent transition, 2) a valid Idris
||| identifier, 3) a combination of (1) and (2) in comma-separated form.
handleAssignment : DOT -> Maybe (List Transition)   -- TODO: List1 ?
handleAssignment (Assign [(NameID "label"), val]) =
  if isValidLabelVal val
     then case tryMultiTrans val of   -- FIXME: do notation?
               (Just ts) => Just ts
               Nothing =>
                  case tryDepTrans val of
                       (Just dt) => Just [dt]
                       Nothing =>
                          case tryRegTrans val of
                               (Just t) => Just [t]
                               Nothing => Nothing
     else Nothing

handleAssignment _ = Nothing

||| An edge in a DOT model of a DSA.
data DDEdge : Type where
  MkDDEdge :  (t    : Transition)
           -> (from : Identifier)
           -> (to   : Identifier)
           -> DDEdge

||| Extract the assignment from an `AttrList` in an edge in a DSA.
handleEdgeAttrList : DOT -> Maybe DOT
handleEdgeAttrList (AttrList [AList [Assign v]]) =
  Just (Assign v)
handleEdgeAttrList _ = Nothing

||| Extract the node name from a `NodeID`, ensuring its a valid Idris name.
handleEdgeNodeID : DOT -> Maybe Identifier
handleEdgeNodeID (NameID n)   = toIdentifier n
handleEdgeNodeID (StringID n) = toIdentifier n
handleEdgeNodeID _ = Nothing

||| Convert an edge in DOT to an edge in a DSA. The DOT describes a valid edge
||| iff it is a directed edge and it has a "label" in its attrlist.
handleEdge : DOT -> Maybe (List DDEdge)
handleEdge (EdgeStmt (NodeID f _) (EdgeRHS [DiGrEdgeOp, t]) (Just (AttrList a))) =
  do assignment <- handleEdgeAttrList (AttrList a)
     transns <- handleAssignment assignment
     from <- handleEdgeNodeID f
     to <- handleEdgeNodeID t
     pure $ map (\t => MkDDEdge t from to) transns

handleEdge _ = Nothing














||| A string describes a dependent edge iff it contains a valid idris name,
||| followed by a '(', followed by a valid idris name, followed by a ')'.
export
isDepEdge : String -> Bool
isDepEdge s =
   let cs = unpack s
   in case span ((==) '(') cs of 
           ([], _) => False
           (_ , []) => False
           (tName, (_ :: cs')) =>
             case span ((==) ')') cs' of
                  ([], _) => False
                  (resName, _) => isValidIdrName tName && isValidIdrName resName

export
labelValOK : String -> Bool
labelValOK v = (isValidIdrName . unpack) v || isDepEdge v

||| Checks that the values given from `toLabel` are valid DSA values. Each
||| value is accepted iff it is a valid Idris name or it is a dependent edge.
export
labelValsOK : (vals : List String) -> {auto 0 ok : NonEmpty vals} -> Bool
labelValsOK [] impossible
labelValsOK [v] = labelValOK v
labelValsOK (v :: (v' :: vs)) = labelValOK v && labelValsOK (v' :: vs)
--labelValsOK vals = all (\v => (isValidIdrName . unpack) v || isDepEdge v) vals

||| Convert the given DOT to a `Label`. Some DOT is a `Label` iff it is an
||| assignment from the name "label" to a StringID consisting of at least one
||| valid transition (see `labelValsOK` for more details on what that means).
export
toLabel : DOT -> Maybe Label
toLabel (Assign [NameID "label", StringID rawVals]) =
  case split (== ',') rawVals of
       (head ::: tail) =>
               let head' = trim head
                   tail' = map trim tail
               in if labelValsOK (head' :: tail')
                     then Just $ MkLabel (fromList (head' :: tail'))
                     else Nothing

toLabel _ = Nothing


||| An edge in a DOT model of a DSA.
export
data LDDEdge : Type where
  ||| The edge must have a `from` node and a `to` node, as well as be labelled
  ||| (in order for the transition it describes to have a name).
  MkLDDEdge :  (from  : Identifier)
            -> (to    : Identifier)
            -> (label : Label)
            -> LDDEdge

export
DOTAble LDDEdge where
  -- "from" is the id of a node;
  -- same with "to", but it is part of the RHS of an edge statement and we only
  -- allow directed edges in DOT diagrams of DSAs;
  -- "l" is the edge's label's values, which need to be wrapped in an `AttrList`
  -- and an `AList` to conform to the DOT grammar.
  toDOT (MkLDDEdge from to label) =
    EdgeStmt (NodeID (NameID from) Nothing)
             (EdgeRHS [DiGrEdgeOp, (NodeID (NameID to) Nothing)])
             (Just $ AttrList [AList [toDOT label]])

||| Convert the given DOT to an identifier. Some DOT is an identifier iff it
||| is either a NameID or a StringID, and if that ID is a valid Idris name.
export
dotToIdentifier : DOT -> Maybe Identifier
dotToIdentifier (NameID   n) = toIdentifier n
dotToIdentifier (StringID s) = toIdentifier s
dotToIdentifier _ = Nothing

||| Convert the given DOT to a `LDDEdge`. Some DOT is an edge in a DSA iff it
||| goes from a `NodeID` to a `NodeID` using a directed edge, with a single
||| attribute detailing the labelling of the edge.
toLDDEdge : DOT -> Maybe LDDEdge
toLDDEdge (EdgeStmt (NodeID f _) (EdgeRHS [DiGrEdgeOp, (NodeID t _)]) (Just (AttrList [AList [attr]]))) =
  do from <- dotToIdentifier f
     to <- dotToIdentifier t
     label <- toLabel attr
     pure (MkLDDEdge from to label)

toLDDEdge _ = Nothing

||| Convert a DOT statement to a part of a DOTDSA. The statement is valid in the
||| DSA iff it is a `Stmt` containing an `EdgeStmt`.
export
handleStmt : DOT -> Maybe LDDEdge
handleStmt (Stmt (EdgeStmt f rhs attrList)) = toLDDEdge (EdgeStmt f rhs attrList)
handleStmt _ = Nothing

||| A slightly more restricted version of DOT for easier conversion to a DSA.
data DOTDSA : Type where
--  DSAGraph : DOTDSA   -- FIXME: refine!
    DSAGraph :  (name  : Identifier)
             -> (edges : List LDDEdge)
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

export covering
toDOTDSA2 : DOT -> IO ()
toDOTDSA2 (Graph False DiGraph (Just n) (StmtList [Stmt (EdgeStmt (NodeID f _) (EdgeRHS [DiGrEdgeOp, (NodeID t _)]) (Just (AttrList [AList [(Assign [NameID "label", (StringID v)])]])))])) =
  do name <- pure $ dotToIdentifier n
     putStrLn $ "Name: " ++ show name
     putStrLn $ "Stmt: " ++ show (EdgeStmt (NodeID f Nothing) (EdgeRHS [DiGrEdgeOp, (NodeID t Nothing)]) (Just (AttrList [AList [(Assign [NameID "label", (StringID v)])]])))
--     es <- pure $ traverse handleStmt ([Stmt stmt])
--     putStrLn $ "Edgy af? " ++ (if isJust es then "Yes" else "No")
     putStrLn $ "f: " ++ show (dotToIdentifier f)
     putStrLn $ "t: " ++ show (dotToIdentifier t)
     putStrLn $ "v=" ++ v
     putStrLn $ "v: " ++ show (labelValOK v)
toDOTDSA2 _ = putStrLn "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH"

