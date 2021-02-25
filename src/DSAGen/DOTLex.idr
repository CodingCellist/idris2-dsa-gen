-- Idris2

module DSAGen.DOTLex

import Data.List
import Text.Lexer

public export
data Token
  -- a keyword is a string
  = Keyword String
  -- an identifier is a string
  | Identifier String
  -- various opening + closing things
  | OBrace      -- {
  | CBrace      -- }
  | OBracket    -- [
  | CBracket    -- ]
  -- an edge between 2 nodes
  | EdgeOp
  -- '=' is an assignment operator
  | AssignmentOp
--  -- literals
--  | Literal String
  -- semicolons are optional, but can occur
  | Semicolon
  -- comments
  | LineComment String
  | BlockComment String

export
Show Token where
  show (Keyword kw) = "Keyword '" ++ kw ++ "'"
  show (Identifier id) = "ID '" ++ id ++ "'"
  show OBrace = "OBrace"
  show CBrace = "CBrace"
  show OBracket = "OBracket"
  show CBracket = "CBracket"
  show EdgeOp = "EdgeOp"
  show AssignmentOp = "AssignmentOp"
--  show (Literal l) = "Lit '" ++ l ++ "'"
  show Semicolon = "Semicolon"
  show (LineComment _) = "LineComment"
  show (BlockComment _) = "BlockComment"

||| DOT keywords: node, edge, graph, digraph, subgraph, strict
keywords : List String
keywords = [ "node"
           , "edge"
           , "graph"
           , "digraph"
           , "subgraph"
           , "strict"
           ]

||| A choice between the different keywords, case insensitive
keyword : Lexer
keyword = choiceMap (\kw => approx kw) keywords

||| At least 1 alpha character [A-Za-z] or underscore
id_opt_1_start : Lexer
id_opt_1_start
  = (alpha <|> is '_') <+> many id_opt_1_start

||| At least 1 alphaNum or underscore
alphaNumsUnders : Lexer
alphaNumsUnders
  =   alphaNums
  <|> some (is '_')

||| Any string of alphaNums or underscores, not beginning with a digit
id_opt_1 : Lexer
id_opt_1
  = id_opt_1_start <+> many alphaNumsUnders

||| A numeral [-]?(.[0-9]+ | [0-9]+(.[0-9]*)?)
id_opt_2 : Lexer
id_opt_2
  =   opt (is '-')
  <+> ((any <+> digits) <|> (digits <+> opt (any <+> many digits)))

||| Any double-quoted string ("...") possibly containing escaped quotes (\")
id_opt_3 : Lexer
id_opt_3 = stringLit

-- there is technically an opt 4: an HTML string, but I can't be bothered
-- implementing that!

||| An identifier is one of its options (see id_opt_N, where N is a number)
identifier : Lexer
identifier
  =   id_opt_1
  <|> id_opt_2
  <|> id_opt_3

||| opening brace: {
oBrace : Lexer
oBrace = is '{'

||| closing brace: }
cBrace : Lexer
cBrace = is '}'

||| An opening bracket: [
oBracket : Lexer
oBracket = is '['

||| A closing bracket: ]
cBracket : Lexer
cBracket = is ']'

||| An edge operator: ->  OR  --
edgeOp : Lexer
edgeOp
  =   (is '-' <+> is '>')
  <|> (is '-' <+> is '-')

||| An assignment operator: =
assignmentOp : Lexer
assignmentOp = is '='

||| A semicolon
semicolon : Lexer
semicolon = is ';'

||| A line comment
dotLineComment : Lexer
dotLineComment
  =   lineComment (exact "//")
  <|> lineComment (is '#')

||| A block comment
dotBlockComment : Lexer
dotBlockComment = blockComment (exact "/*") (exact "*/")


||| Pairs of Lexers to match and String -> Token functions to use in case the
||| Lexer matches
tokMap : TokenMap Token
tokMap
  = [ (keyword, \str => Keyword str)
    , (identifier, \str => Identifier str)
    , (oBrace, (const OBrace))
    , (cBrace, (const CBrace))
    , (oBracket, (const OBracket))
    , (cBracket, (const CBracket))
    , (edgeOp, (const EdgeOp))
    , (assignmentOp, (const AssignmentOp))
    , (semicolon, (const Semicolon))
    , (dotLineComment, \str => LineComment str)
    , (dotBlockComment, \str => BlockComment str)
--    , (space, (const LineComment "(32)"))
    ]

||| Given a string to lex, returns the list of recognised tokens and the
||| position and remaining string reached.
export
lex : String -> (List (TokenData Token), (Int, Int, String))
lex str = lex tokMap str

