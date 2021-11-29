module DSAGen.DOTDSA

import Graphics.DOT

import Data.List
import Data.List1
import Data.Vect
import Data.String

%default total

-- TODO: Should possibly be an interface in `dot-parse`?
interface DOTAble a where
  toDOT : a -> DOT

-- TODO: prove that there was a "label" keyword on creation?
||| Labels are just strings, but we only create them from a "label" keyword
Label : Type
Label = String

DOTAble Label where
  toDOT l = Assign [(NameID "label"), (StringID l)]

-- FIXME: what's the right name?
Identifier : Type
Identifier = String

DOTAble Identifier where
  -- i never contains spaces (FIXME: assumption), so no need to use `StringID`
  toDOT i = NameID i

||| A valid Idris name is at least one aplhabetical character followed by a
||| number of alphanumerical or underscore characters.
isValidIdrName : List Char -> Bool
isValidIdrName [] = False
isValidIdrName (c :: cs) = isAlpha c && all (\c => isAlphaNum c || c == '_') cs

||| If the DOT was `label="<value>"`, then we can extract the `Label`.
toLabel : (id_ : String) -> Maybe Label
toLabel id_ = toMaybe (isValidIdrName $ unpack id_) id_

||| Returns the given string in a `Just` iff it is a valid Idris name.
toIdentifier : (s : String) -> Maybe Identifier
toIdentifier = toLabel

||| A slightly more restricted version of DOT for easier conversion to a DSA.
data DOTDSA : Type where
  DSAGraph : DOTDSA   -- FIXME: refine!

||| A dependent transition consists of the name of the transition, and the
||| accepted dependent result which allows the transition to happen. A regular
||| transition has no dependent result.
data Transition : Type where
  MkTransition :  (tName   : Identifier)
               -> (resName : Maybe Identifier)
               -> Transition

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
handleEdge (EdgeStmt (NodeID n _) rhs (Just (AttrList a))) =
  do a' <- handleEdgeAttrList (AttrList a)
     ts <- handleAssignment a'
     ?handleEdge_rhs_21

handleEdge _ = Nothing


