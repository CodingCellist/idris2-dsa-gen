module DSAGen.Label.Lexer

import Text.Lexer

%default total

-- Example edge label values:
--   Send:(SeqNo sn)
--   Wait?(Timeout)
--   Wait?(Ack sn)
--   Next!(SeqNo (sn + 1))
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

--- ||| An edge symbol is one of:
--- |||   :
--- |||   ?
--- |||   !
--- edgeSymbol : Lexer
--- edgeSymbol = colon <|> query <|> bang

||| Any alphanumerical character, or an underscore.
alphaUnder : Lexer
alphaUnder = alpha <|> is '_'

||| Left parenthesis '('.
lParens : Lexer
lParens = is '('

||| Right parenthesis ')'.
rParens : Lexer
rParens = is ')'

||| An Idris name is at least one alphabetical character followed by a number of
||| alphanumerical or underscore characters.
idrName : Lexer
idrName = alpha <+> many alphaUnder

||| A data constructor is at least one UPPERCASE alphabetical character,
||| followed by a number of alphanumerical or underscore characters.
dataCons : Lexer
dataCons = upper <+> many alphaUnder

--- ||| A command name is a data constructor
--- %inline
--- cmdName : Lexer
--- cmdName = dataCons
--- 
--- ||| A result name is a data constructor
--- %inline
--- resName : Lexer
--- resName = dataCons
--- 
--- ||| A data constructor which contains arguments (args) must have those args be
--- ||| either data constructors or Idris names. There must be at least one
--- ||| argument.
--- dataArgs : Lexer
--- dataArgs = dataCons <+> spaces <+> anArg <+> many (spaces <+> anArg)
---   where
---     anArg : Lexer
---     anArg = idrName <|> dataCons
--- 
--- ||| Argument notation (for any of the edge symbols) is:
--- |||   A left parens, a result name (optionally taking some valid Idris names as
--- |||   arguments), and a right parens.
--- argNotation : Lexer
--- argNotation =  lParens
---            <+> (dataArgs <|> dataCons)
---            <+> rParens
--- 
--- ||| Taking a value as an argument is denoted by:
--- |||   A colon, followed by: a left parens, a result name (optionally taking some
--- |||   valid Idris names as arguments), and a right parens.
--- valArg : Lexer
--- valArg = colon <+> argNotation
--- 
--- ||| Depending on a value is denoted by:
--- |||   A question-mark, followed by: a left parens, a result name (optionally
--- |||   taking some valid Idris names as arguments), and a right parens.
--- depVal : Lexer
--- depVal = query <+> argNotation
--- 
--- ||| Producing a value as a result is denoted by:
--- |||   An exclamation-mark, followed by: a left parens, a result name (optionally
--- |||   taking some valid Idris names as arguments), and a right parens.
--- prodVal : Lexer
--- prodVal = bang <+> argNotation
--- 
--- ||| A value notation is one of:
--- |||   * a value argument
--- |||   * a dependent value
--- |||   * a produced value
--- valNotation : Lexer
--- valNotation =  valArg <|> depVal <|> prodVal
--- 
--- ||| The possible value notation combinations are:
--- |||   * a value argument, followed by a dependent value, followed by a produced
--- |||     value;
--- |||   * a value argument, followed by a dependent value;
--- |||   * a value argument, followed by a produced value;
--- |||   * a dependent argument, followed by a produced value.
--- valCombns : Lexer
--- valCombns =  (valArg <+> depVal <+> prodVal)    -- :(test)?(rest)!(quest)
---          <|> (valArg <+> depVal)                -- :(test)?(rest)
---          <|> (valArg <+> prodVal)               -- :(test)!(quest)
---          <|> (depVal <+> prodVal)               -- ?(rest)!(quest)
--- 
--- ||| A command with arguments is a command name followed by either:
--- |||   * a combination of value notations;
--- |||   * a single value notation (i.e. either: `valArg`, `depVal`, or `prodVal`).
--- cmdWithArgs : Lexer
--- cmdWithArgs = cmdName <+> (valCombns <|> valNotation)
--- 
--- ||| A label is either a plain command name, or a command with arguments.
--- label : Lexer
--- label = cmdName <|> cmdWithArgs

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

