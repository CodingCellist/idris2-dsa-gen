module DSAGen.DOTDSA

import Graphics.DOT

import Data.List
import Data.Vect
import Data.SnocList

%default total

-- TODO: Should possibly be an interface in `dot-parse`?
interface DOTAble a where
  toDOT : a -> DOT

-- TODO: prove that we only create them from "label"?
||| Labels are just strings, but we only create them from a "label" keyword
Label : Type
Label = String

DOTAble Label where
  toDOT l = Assign [(NameID "label"), (StringID l)]

-- FIXME: what's the right name?
Identifier : Type
Identifier = String

DOTAble Identifier where
  -- i never contains spaces (FIXME: assumption), so no need to be a `StringID`
  toDOT i = NameID i

||| A valid Idris name is at least one aplhabetical character followed by a
||| number of alphanumerical or underscore characters.
isValidIdrName : List Char -> Bool
isValidIdrName [] = False
isValidIdrName (c :: cs) = isAlpha c && all (\c => isAlphaNum c || c == '_') cs

||| If the DOT was `label="<value>"`, then we can extract the `Label`.
toLabel : DOT -> Maybe Label
toLabel (NameID id) = if (isValidIdrName . unpack) id
                            then Just id
                            else Nothing
toLabel (StringID id) = if (isValidIdrName . unpack) id
                              then Just id
                              else Nothing
toLabel _ = Nothing

||| A slightly more restricted version of DOT for easier conversion to a DSA
data DOTDSA : Type where
  DSAGraph : DOTDSA   -- FIXME: refine!

||| A dependent transition
data DepTrans : Type where
  MkDepTrans :  (tName : Identifier)
             -> (resName : Identifier)
             -> DepTrans

||| Return a `DepTrans` iff the input is a `StringID id` and the `id` has the
||| form "<tName>(<resName>)", for example:
||| (StringID "CheckPIN(Incorrect)")
toDepTrans : DOT -> Maybe DepTrans
toDepTrans (StringID id) =
  let cs = unpack id
  in case span ((==) '(') cs of 
          ([], _) => Nothing
          (_ , []) => Nothing
          (tName, (_ :: cs')) =>
            case span ((==) ')') cs' of
                 ([], _) => Nothing
                 (resName, _) =>
                      if isValidIdrName tName && isValidIdrName resName
                         then Just $ MkDepTrans (pack tName) (pack resName)
                         else Nothing

toDepTrans _ = Nothing

||| An edge in a DOT model of a DSA
data DDEdge : Type where
  ||| A regular (non-dependent) edge
  MkDDEdge : (name : Label) -> (from : Identifier) -> (to : Identifier) -> DDEdge
  ||| A dependent edge
  MkDepDDEdge :  DepTrans
              -> (from : Identifier)
              -> (to : Label)
              -> DDEdge

||| Assignment in DOT is a valid DSA thing, iff it assigns a "label" AND that
||| label is either a dependent transition description, or a valid Idris
||| identifier.
handleAssignment : DOT -> Maybe (Either Label DepTrans)
handleAssignment (Assign [(NameID "label"), val]) =
  case toDepTrans val of
       Nothing =>
          case toLabel val of
               Nothing => Nothing
               (Just label) => Just $ Left label
       (Just depTrans) => Just $ Right depTrans
handleAssignment _ = Nothing
-- FIXME: RESUME HERE
-- FIXME: This needs to deal with the possibility of the assignment containing
--        multiple values (probably need to use `words`), e.g.
--        label="GetPIN, CheckPIN(Incorrect)"

||| Convert the given DOT to a DSA Edge, if everything is okay.
||| See also: `handleAssignment`, `toLabel`.
toDDEdge : DOT -> Maybe DDEdge
toDDEdge (EdgeStmt (NodeID from _) (EdgeRHS [DiGrEdgeOp, (NodeID to _)]) (Just (AttrList [(AList [attr])]))) =
  let mFrom  = toLabel from
      mTo    = toLabel to
      mEType = handleAssignment attr
  in if isJust mFrom && isJust mTo && isJust mEType
        then case !mEType of
                  (Left label) =>
                      Just $ MkDDEdge label (!mFrom) (!mTo)
                  (Right depTrans) =>
                      Just $ MkDepDDEdge depTrans (!mFrom) (!mTo)
        else Nothing

toDDEdge _ = Nothing

