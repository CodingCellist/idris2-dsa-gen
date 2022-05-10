module DSAGen.Label.Lexer

import public Text.Lexer

%default total

-- Example edge label values:
--   Send:(SeqNo sn)
--   Wait?(Timeout)
--   Wait?(Ack sn)
--   Next!(SeqNo (sn + 1))    /!\ need to be able to lex expr.n symbols + lit.s!
--   CheckPIN:(PIN)?(Incorrect)

||| Colon means "take value as argument".
colon : Lexer
colon = is ':'

||| Query/Question-mark means "depend on the value".
query : Lexer
query = is '?'

||| Bang/Exclamation-mark means "produce value".
bang : Lexer
bang = is '!'

||| Left parenthesis '('.
lParens : Lexer
lParens = is '('

||| Right parenthesis ')'.
rParens : Lexer
rParens = is ')'

||| Tuple separator
comma : Lexer
comma = is ','

||| Numerical literals
numLit : Lexer
numLit = (opt $ is '-') <+> some digit

||| Addition '+'
addOp : Lexer
addOp =  is '+'

||| Any alphanumerical character, or an underscore.
alphaUnder : Lexer
alphaUnder = alpha <|> is '_'

||| An Idris name is at least one lowercase alphabetical character followed by a
||| number of alphanumerical or underscore characters.
idrName : Lexer
idrName = lower <+> many alphaUnder

||| A data constructor is at least one UPPERCASE alphabetical character,
||| followed by a number of alphanumerical or underscore characters.
dataCons : Lexer
dataCons = upper <+> many alphaUnder

||| A label may contain:
|||   * a data constructor
|||   * an Idris name
|||   * a left parenthesis
|||   * a right parenthesis
|||   * a colon
|||   * a question-mark
|||   * an exclamation-mark
|||   * some whitespace
public export
data LabelTok
  = DataCons String
  | IdrName String
  | NumLit String
  | LParens
  | RParens
  | AddOp
  | Colon
  | Comma
  | Query
  | Bang
  | WS

export
Show LabelTok where
  show (DataCons c) = "(DataCons " ++ c ++ ")"
  show (IdrName n) = "(IdrName " ++ n ++ ")"
  show (NumLit l) = "(NumLit " ++ l ++ ")"
  show LParens = "LParens"
  show RParens = "RParens"
  show AddOp = "AddOp"
  show Colon = "Colon"
  show Comma = "Comma"
  show Query = "Query"
  show Bang = "Bang"
  show WS = "WS"

||| A mappping from the various lexers to a function of type
|||   String -> LabelTok
labelTokenMap : TokenMap LabelTok
labelTokenMap = [ (spaces  , const WS)
                , (comma   , const Comma)
                , (colon   , const Colon)
                , (query   , const Query)
                , (bang    , const Bang)
                , (addOp   , const AddOp)
                , (lParens , const LParens)
                , (rParens , const RParens)
                , (numLit  , \l => NumLit l)
                , (idrName , \n => IdrName n)
                , (dataCons, \c => DataCons c)
                ]

export
lex : String -> (List (WithBounds LabelTok), (Int, (Int, String)))
lex label = lex labelTokenMap label

