module DSAGen.Label.Lexer

import Text.Lexer

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
  | LParens
  | RParens
  | Colon
  | Query
  | Bang
  | WS

export
Show LabelTok where
  show (DataCons c) = "(DataCons " ++ c ++ ")"
  show (IdrName i) = "(IdrName " ++ i ++ ")"
  show LParens = "LParens"
  show RParens = "RParens"
  show Colon = "Colon"
  show Query = "Query"
  show Bang = "Bang"
  show WS = "WS"

||| A mappping from the various lexers to a function of type
|||   String -> LabelTok
labelTokenMap : TokenMap LabelTok
labelTokenMap = [ (spaces  , const WS)
                , (colon   , const Colon)
                , (query   , const Query)
                , (bang    , const Bang)
                , (lParens , const LParens)
                , (rParens , const RParens)
                , (idrName , \n => IdrName n)
                , (dataCons, \c => DataCons c)
                ]

export
lex : String -> (List (WithBounds LabelTok), (Int, (Int, String)))
lex label = lex labelTokenMap label

