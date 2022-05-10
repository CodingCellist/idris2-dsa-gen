module DSAGen.DOTDSA

import Graphics.DOT

import DSAGen.DSL
import DSAGen.Lexer
import DSAGen.Parser

import Data.List
import Data.List1
import Data.Vect
import Data.String
import Data.SnocList
import Data.Either


%default total


------------------------------------
-- DOTDSA datatype and components --
------------------------------------

---- -- TODO: prove that string is non-empty? and/or that it's a valid Idris name?
---- ||| Labels are lists of at least one string.
---- export
---- data DDLabel : Type where
----   MkDDLabel : (vals : Vect (S k) String) -> DDLabel

-- FIXME: is this the right name for this?
export
DDIdentifier : Type
DDIdentifier = String

||| An edge in a DOT model of a DSA.
export
data DDEdge : Type where
  ||| The edge must have a `from` node and a `to` node, as well as be labelled
  ||| (in order for the transition it describes to have a name).
  MkDDEdge :  (from  : DDIdentifier)
           -> (to    : DDIdentifier)
           -> (label : List1 DSALabel)
           -> DDEdge

||| A slightly more restricted version of DOT for easier conversion to a DSA.
export
data DOTDSA : Type where
    DSAGraph :  (name  : DDIdentifier)
             -> (edges : List DDEdge)
             -> {auto 0 ok : NonEmpty edges}
             -> DOTDSA

||| The errors that can appear when checking if a DOT graph is a DOTDSA
data DOTDSAErr : Type where
  ||| The given string is not a valid Idris name
  InvalidIdrName : (invName : String) -> DOTDSAErr
  ||| The given string was improperly formatted (e.g. missing a parens)
  StringFormatErr : (str : String) -> DOTDSAErr
  ||| The given DOT identifier cannot be converted to a DOTDSA identifier
  IncompatibleDOTIDErr : (dotID : DOTID) -> DOTDSAErr
  ||| There was an error in the label
  LabelErr : Assign -> (reason : Maybe DOTDSAErr) -> DOTDSAErr
  ||| There was a problem with the label value
  LabelValErr : (val : String) -> DOTDSAErr
  ||| The assignment was not a label
  NotLabelErr : Assign -> DOTDSAErr
  ||| There was an error lexing the label
  LabelLexErr : (rem : String) -> DOTDSAErr
  ||| There was an error parsing the label
  LabelParseErr : List1 (ParsingError LabelTok) -> DOTDSAErr
  ||| The entire label couldn't be parsed
  LabelRemErr : (rem : List (WithBounds LabelTok)) -> DOTDSAErr
  ||| The edge statement was malformatted
  EdgeStmtFormatErr : (edgeStmt : Stmt) -> DOTDSAErr
  ||| The statement was not an edge statement
  NotEdgeStmtErr : (stmt : Stmt) -> DOTDSAErr
  ||| There was a problem with the DOT graph
  DOTGraphErr : (g : Graph) -> DOTDSAErr
  ||| Tried to process a graph with no statements
  EmptyStmtsErr : (g : Graph) -> DOTDSAErr

----------------------
-- Util and filters --
----------------------

||| A valid Idris name is at least one alphabetical character followed by a
||| number of alphanumerical or underscore characters.
isValidIdrName : List Char -> Bool
isValidIdrName [] = False
isValidIdrName (c :: cs) = isAlpha c && all (\c => isAlphaNum c || c == '_') cs

---- ||| A string describes a dependent edge iff it contains a valid idris name,
---- ||| followed by a '(', followed by a valid idris name, followed by a ')'.
---- isDepEdge : String -> Bool
---- isDepEdge s =
----   -- FIXME: fix words' totality
----   -- let cs = unpack $ concat (map trim (assert_total $ words s))  
----   let cs = unpack s
----   in case span (/= '(') cs of 
----          ([], _) => False
----          (_ , []) => False
----          (tName, (_ :: cs')) =>       -- ignore the '(' which is included by `span`
----              case Lin <>< cs' of
----                   resName :< ')' =>   -- check that we close the parenthesis
----                       isValidIdrName tName && isValidIdrName (toList resName)
----                   _ => False
---- 
---- ||| Checks that the values given from `toLabel` are valid DSA values. Each
---- ||| value is accepted iff it is a valid Idris name or it is a dependent edge.
---- labelValsOK : (vals : List1 String) -> Bool
---- labelValsOK vals = all (\v => (isValidIdrName . unpack) v || isDepEdge v) vals

||| Remove the leading and trailing '"' of the `str` contained in a DOT's `StringID`.
cleanStringID : String -> String
cleanStringID id_ = substr 1 ((length id_) `minus` 2) id_
                             -- substr is 0-based  ^


-------------------
-- LABEL VERSION --
-------------------

||| Try to lex the given label string to a series of `LabelTok`s.
|||
||| The entire string must be lexed for the function to succeed, otherwise a
||| `DOTDSAErr` containing the remainder is returned.
lexLabel : (rawLabel : String) -> Either DOTDSAErr (List (WithBounds LabelTok))
lexLabel rawLabel = do let (toks, (_, _, rawRem)) = lex rawLabel
                       True <- pure $ rawRem == ""
                         | False => Left (LabelLexErr rawRem)
                       pure toks

||| Try to parse the given list of `LabelTok`s as a label.
|||
||| The entire list of tokens must be parsed for the function to succeed. If
||| some parsing errors occur, they are wrapped in a `DOTDSAErr` and returned.
||| If the remainder is non-empty, it is returned in a different `DOTDSAErr`.
parseLabel :  (labelToks : List (WithBounds LabelTok))
           -> Either DOTDSAErr DSALabel
parseLabel labelToks = do let Right (dsaLabel, rem) = parse labelToks
                                | Left errs => Left (LabelParseErr errs)
                          case rem of
                               [] => pure dsaLabel
                               _  => Left (LabelRemErr rem)

||| Try to convert the given label string to a list of `DSALabel` commands.
dsaLabel : (rawLabel : String) -> Either DOTDSAErr (List1 DSALabel)
dsaLabel rawLabel = do let rawCmds = trim <$> split (== ';') rawLabel
                       lexedCmds <- traverse lexLabel rawCmds
                       traverse parseLabel lexedCmds


--------------------
-- DOT ==> DOTDSA --
--------------------

||| Try to convert the given DOT assignment to a list of `DSALabel` commands.
|||
||| An assignment is a DSALabel iff its left hand side is the `NameID` "label",
||| and its right hand side is a `StringID` which  can be parsed as a list of
||| commands.
export
assignToDSALabel : Assign -> Either DOTDSAErr (List1 DSALabel)
assignToDSALabel (MkAssign (NameID "label") (StringID rawLabel)) = dsaLabel rawLabel
assignToDSALabel a = Left (NotLabelErr a)

--- ||| Convert the given DOT assignment to a `DDLabel`. Some DOT is a `DDLabel` iff
--- ||| it is an assignment from the name "label" to a StringID consisting of at
--- ||| least one valid transition (see `labelValsOK` for more details on what that
--- ||| means).
--- export
--- toDDLabel : Assign -> Maybe DDLabel
--- toDDLabel (MkAssign (NameID "label") (StringID rawVals)) =
---   case split (== ',') (cleanStringID rawVals) of
---        (head ::: tail) =>
---                let head' = trim head
---                    tail' = map trim tail
---                in if labelValsOK (head' ::: tail')
---                      then Just $ MkDDLabel (fromList (head' :: tail'))
---                      else Nothing
--- 
--- toDDLabel _ = Nothing


||| Returns the given string in a `Just` iff it is a valid Idris name.
toIdentifier : (s : String) -> Either DOTDSAErr DDIdentifier
toIdentifier s = if isValidIdrName $ unpack s
                    then pure s
                    else Left $ InvalidIdrName s

||| Convert the given DOTID to a `DDIdentifier`. Some DOTID is a `DDIdentifier`
||| iff it is either a NameID or a StringID, and if that ID is a valid Idris
||| name.
export
dotToIdentifier : DOTID -> Either DOTDSAErr DDIdentifier
dotToIdentifier (NameID   n) = toIdentifier n
dotToIdentifier (StringID s) = toIdentifier (cleanStringID s)
dotToIdentifier dotID = Left $ IncompatibleDOTIDErr dotID

||| Convert the given DOT statement to a `DDEdge`. Some statement is an edge in
||| a DSA iff it goes from a `NodeID` to a `NodeID` using a directed edge, with
||| a single attribute detailing the labelling of the edge.
|||
||| @ stmt the statement to convert
export
toDDEdge : (stmt : Stmt) -> Either DOTDSAErr DDEdge
toDDEdge (EdgeStmt (Left (MkNodeID f _)) ((MkEdgeRHS Arrow (Left (MkNodeID t _))) ::: []) [[attr]]) =
   do let Right from = dotToIdentifier f
            | Left fromErr => Left fromErr
      let Right to = dotToIdentifier t
            | Left toErr => Left toErr
      let Right labelCmds = assignToDSALabel attr
            | Left labelErr => Left labelErr
      pure (MkDDEdge from to labelCmds)
 
toDDEdge stmt@(EdgeStmt _ _ _) = Left $ EdgeStmtFormatErr stmt
toDDEdge stmt = Left $ NotEdgeStmtErr stmt

||| Convert a DOT statement to a part of a DOTDSA. The statement is valid in the
||| DSA iff it is a `Stmt` containing an `EdgeStmt`.
|||
||| @ stmt the statement to convert
export
handleStmt : Stmt -> Either DOTDSAErr DDEdge
handleStmt (EdgeStmt f rhs attrList) = toDDEdge (EdgeStmt f rhs attrList)
handleStmt stmt = Left $ NotEdgeStmtErr stmt


||| Convert the given DOT Graph to the subset `DOTDSA`, which describes a DSA.
export
toDOTDSA : Graph -> Either DOTDSAErr DOTDSA
toDOTDSA g@(MkGraph Nothing DigraphKW (Just n) stmts) =
  do let Right name = dotToIdentifier n
          | Left nameErr => Left nameErr
     let traversed = traverse handleStmt stmts
     case traversed of
          (Left err) => Left err
          (Right []) => Left $ (EmptyStmtsErr g)
          (Right (e :: es)) => pure (DSAGraph name (e :: es))

toDOTDSA g = Left $ DOTGraphErr g

---- toDOTDSA (MkGraph Nothing DigraphKW (Just n) stmts) =
----   do let Right name = dotToIdentifier n
----           | Left nameErr => Left nameErr
----      (e :: es) <- traverse handleStmt stmts
----      pure (DSAGraph name (e :: es))
---- 
---- toDOTDSA g = Left $ DOTGraphErr g


-----------------------------------
-- Interfaces for DOTDSA ==> DOT --
-----------------------------------

---- export
---- DOTAssign DDLabel where
----   toAssign (MkDDLabel vals) =
----     -- each of the values must be comma-separated
----     let valStr = foldr1 (++) $ intersperse ", " vals
----     in MkAssign (NameID "label") (StringID valStr)

export
DOTDOTID DDIdentifier where
  -- i never contains spaces (FIXME: assumption), so no need to use `StringID`
  toDOTID i = NameID i

export
covering
DOTStmt DDEdge where
  -- "from" is the id of a node;
  -- same with "to", but it is part of the RHS of an edge statement and we only
  -- allow directed edges in DOT diagrams of DSAs;
  -- "l" is the edge's label's values, which need to be wrapped in an `AttrList`
  -- and an `AList` to conform to the DOT grammar.
  toStmt (MkDDEdge from to label) =
    EdgeStmt (Left (MkNodeID (toDOTID from) Nothing))
             ((MkEdgeRHS Arrow (Left (MkNodeID (NameID to) Nothing))) ::: [])
             ([[toAssign label]])

export
covering
DOTGraph DOTDSA where
  -- A DOTDSA is non-strict, directed graph;
  -- which _does_ have a name;
  -- and whose statements are a list of edge-statements, each of which needs to
  -- be wrapped in a `Stmt` to conform to the DOT grammar.
  toGraph (DSAGraph name edges) =
    MkGraph (Just StrictKW) DigraphKW
            (Just (NameID name))
            (map toStmt edges)


--------------------
-- DOTDSA ==> DSA --
--------------------

||| Add the `from` state of the given `DDEdge` to the accumulator, if it's not
||| already present.
addState : (dde : DDEdge) -> (acc : List State) -> List State
addState (MkDDEdge from to _) acc =
  let fState = newState from
      tState = newState to
      acc' = addIfMissing fState acc
  in addIfMissing tState acc'
  where
    addIfMissing : (s : State) -> (acc : List State) -> List State
    addIfMissing s acc = if elem s acc then acc else s :: acc

||| Given a list of dependent edges and an accumulator, traverse the edges and
||| extract the unique states.
||| See also: `addState`
genStates : (ddes : List DDEdge) -> (acc : List State) -> List State
genStates [] acc = acc
genStates (dde :: ddes) acc =
  let acc' = addState dde acc
  in genStates ddes acc'

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
partitionDDEdges [] = ([], [])
partitionDDEdges ((MkDDEdge from to ((PlainCmd cmd) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_3
partitionDDEdges ((MkDDEdge from to ((TakeCmd cmd arg) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_4
partitionDDEdges ((MkDDEdge from to ((DepCmd cmd dep) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_5
partitionDDEdges ((MkDDEdge from to ((ProdCmd cmd res) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_6
partitionDDEdges ((MkDDEdge from to ((TDCmd cmd arg dep) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_7
partitionDDEdges ((MkDDEdge from to ((TPCmd cmd arg res) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_8
partitionDDEdges ((MkDDEdge from to ((DPCmd cmd dep res) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_9
partitionDDEdges ((MkDDEdge from to ((TDPCmd cmd arg dep res) ::: tail)) :: ddes) = ?partitionDDEdges_rhs_10

---- -- partitionDDEdges : (ddes : List DDEdge) -> (List DDEdge, List DDEdge)
---- partitionDDEdges [] = ([], [])
---- partitionDDEdges (dde :: ddes) =
----   let (deps     , regs    ) = splitEdge dde
----       (moreDeps , moreRegs) = unzipWith splitEdge ddes
----   -- combine all the lists of lists into one big list (for deps and regs respectively)
----   in ( deps ++ foldr (++) [] moreDeps
----      , regs ++ foldr (++) [] moreRegs )
----   where
----     ||| Split the label's values into dependent and regular values.
----     splitLabelVals :  (vals : List1 String)
----                    -> (acc  : (List String, List String))
----                    -> (List String, List String)
----     splitLabelVals (v ::: []) (ds, rs) =
----       if isDepEdge v
----          then (v :: ds , rs     )
----          else (ds      , v :: rs)
----     splitLabelVals (v ::: vs@(_ :: _)) (ds, rs) =
----       if isDepEdge v
----          then let acc' = (v :: ds , rs     ) in splitLabelVals vs acc'
----          else let acc' = (ds      , v :: rs) in splitLabelVals vs acc'
---- 
----     ||| Split a single DDEdge into potentially multiple edges: dependent edges
----     ||| and regular edges.
----     splitEdge : DDEdge -> (List SingleDDEdge, List SingleDDEdge)
----     -- splitEdge : DDEdge -> (List DDEdge, List DDEdge)
----     splitEdge (MkDDEdge from to label) =
----       let (depVals, regVals) = splitLabelVals label ([], [])
----           partialDDEdge = \s => MkSDDE from to [s]
----       in (map partialDDEdge depVals, map partialDDEdge regVals)

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

||| A `RegEdge` is a universal edge candidate wrt. the given `RegEdge` iff the
||| two have the same name and destination/to `State`, but **different**
||| origins/from `State`s.
isUECandidate : (re : RegEdge) -> (cand : RegEdge) -> Bool
isUECandidate (MkRegEdge n1 f1 t1) (MkRegEdge n2 f2 t2) =
  n1 == n2 && f1 /= f2 && t1 == t2

||| Filter the universal edge candidates.
|||
||| A universal edge candidate is an edge which has the same name as the given
||| regular edge, but which doesn't originate from the same `State`
export
filterUECands : (re : RegEdge) -> List RegEdge -> List RegEdge
filterUECands re es =
  filter (isUECandidate re) es

||| A regular edge is a universal edge iff there exists as many universal edge
||| candidates (see `isUECandidate`) as there are states in the DSA.
|||
||| The logic for this is that if you have as many regular edges with the same
||| name and destination as the potential universal edge, but all starting at
||| different edges, then you can always travel along that edge no matter the
||| current state, and so the edge is a universal edge.
isUniversalEdge : (re : RegEdge) -> (es : List RegEdge) -> (dsaStates : List State) -> Bool
isUniversalEdge re@(MkRegEdge _ _ to) es dsaStates =
  let cands = filterUECands re es
      destState = filter (== to) dsaStates
      -- remember that we have extracted one candidate: the `re`
      nCands = length cands + 1
      nStates = length dsaStates
  in nStates == nCands            -- EITHER we have as many states as candidates
     || (length destState == 1    -- OR we better only have one destination...
          && (minus nStates 1 == nCands)) -- ...which is the one we're going to

||| Convert a regular edge to a universal edge: Replace the edge's `from` with
||| `AnyState`.
toUniversalEdge : (re : RegEdge) -> RegEdge
toUniversalEdge (MkRegEdge name _ to) = MkRegEdge name AnyState to

||| Partition the given list of regular edges into a list containing the
||| universal edges, a list containing the remaining regular edges
export
partitionUniversalEdges :  (regEs : List RegEdge)
                        -> (dsaStates : List State)
                        -> (List RegEdge, List RegEdge)
partitionUniversalEdges [] _ = ([], [])
partitionUniversalEdges (re :: res) dsaStates =
  if isUniversalEdge re res dsaStates
     then let ue = toUniversalEdge re
              -- keep only the edges that weren't UE candidates, since we have
              -- replaced the others with a single UE
              rest = filter (\e => not $ isUECandidate re e) res
              -- handle the potential remainder
              (recUEs, recREs) =
                partitionUniversalEdges (assert_smaller (re :: res) rest) dsaStates
          in (ue :: recUEs, recREs)

     else let (recUEs, recREs) = partitionUniversalEdges res dsaStates
          in (recUEs, re :: recREs)

export
DSADesc DOTDSA where
  toDSA (DSAGraph name ddEdges) =
    let dsaName = toUpper name
        dsaStates = genStates ddEdges []
        (rawDEs, rawREs) = partitionDDEdges ddEdges
        (ues, res) = partitionUniversalEdges (map toRegEdge rawREs) dsaStates
        regEdges = ues ++ res
        depEdges = combineDepEdges $ map toDepEdge rawDEs
    in MkDSA dsaName dsaStates regEdges depEdges

