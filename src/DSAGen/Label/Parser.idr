module DSAGen.Label.Parser

import DSAGen.Label.Lexer

import Text.Parser

%default total

-- TODO
data DSALabel : Type where


---------------
-- Terminals --
---------------

lParens : Grammar _ LabelTok True ()
lParens = terminal "Expected '('"
            (\case LParens => Just ()
                   _       => Nothing)

rParens : Grammar _ LabelTok True ()
rParens = terminal "Expected ')'"
            (\case RParens => Just ()
                   _       => Nothing)

colon : Grammar _ LabelTok True ()
colon = terminal "Expected ':'"
          (\case Colon => Just ()
                 _     => Nothing)

query : Grammar _ LabelTok True ()
query = terminal "Expected '?'"
          (\case Query => Just ()
                 _     => Nothing)

bang : Grammar _ LabelTok True ()
bang = terminal "Expected '!'"
          (\case Bang => Just ()
                 _     => Nothing)

||| Whitespace
ws : Grammar _ LabelTok True ()
ws = terminal "Expected some whitespace"
        (\case WS => Just ()
               _  => Nothing)

||| A data constructor
dataCons : Grammar _ LabelTok True DSALabel
dataCons = terminal "Expected a data constructor"
            (\case DataCons d => Just ?dataConsDSA
                   _          => Nothing)

||| A command name is a data constructor
%inline
cmdName : Grammar _ LabelTok True DSALabel
cmdName = dataCons

||| An Idris name
idrName : Grammar _ LabelTok True DSALabel
idrName = terminal "Expected an Idris name"
            (\case IdrName n => Just ?idrNameDSA
                   _          => Nothing)

-------------------
-- Non-terminals --
-------------------

||| A data constructor which contains arguments (args) must have those args be
||| either data constructors or Idris names, separated by whitespace. There must
||| be at least one argument.
dataArgs : Grammar _ LabelTok True DSALabel
dataArgs =
  do args <- some arg
     pure ?dataArgs_rhs
  where
    arg : Grammar _ LabelTok True DSALabel
    arg = do ws
             (idrName <|> dataCons)

||| Argument notation (for any of the edge symbols) is:
|||   A left parens, a result name (optionally taking some valid Idris names as
|||   arguments), and a right parens.
argNotation : Grammar _ LabelTok True DSALabel
argNotation =
  do lParens
     dc <- dataCons
     dArgs <- optional dataArgs
     rParens
     pure ?argNotation_rhs

||| Taking a value as an argument is denoted by:
|||   A colon, followed by: a left parens, a result name (optionally taking some
|||   valid Idris names as arguments), and a right parens.
valArg : Grammar _ LabelTok True DSALabel
valArg = do colon
            arg <- argNotation
            pure ?valArg_rhs

||| Depending on a value is denoted by:
|||   A question-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
depVal : Grammar _ LabelTok True DSALabel
depVal = do query
            val <- argNotation
            pure ?depVal_rhs

||| Producing a value as a result is denoted by:
|||   An exclamation-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
prodVal : Grammar _ LabelTok True DSALabel
prodVal = do bang
             val <- argNotation
             pure ?prodVal_rhs

||| A value notation is one of:
|||   * a value argument
|||   * a dependent value
|||   * a produced value
valNotation : Grammar _ LabelTok True DSALabel
valNotation =  valArg
           <|> depVal
           <|> prodVal

||| A value argument, followed by a dependent value, followed by a produced
||| value.
argDepProd : Grammar _ LabelTok True DSALabel
argDepProd = do vArg <- valArg
                dVal <- depVal
                pVal <- prodVal
                pure ?argDepProd_rhs

||| A value argument, followed by a dependent value.
argDep : Grammar _ LabelTok True DSALabel
argDep = do vArg <- valArg
            dVal <- depVal
            pure ?argDep_rhs

||| A value argument, followed by a produced value.
argProd : Grammar _ LabelTok True DSALabel
argProd = do vArg <- valArg
             pVal <- prodVal
             pure ?argProd_rhs

||| A dependent argument, followed by a produced value.
depProd : Grammar _ LabelTok True DSALabel
depProd = do dVal <- depVal
             pVal <- prodVal
             pure ?depProd_rhs

||| The possible value notation combinations are:
|||   * a value argument, followed by a dependent value, followed by a produced
|||     value;
|||   * a value argument, followed by a dependent value;
|||   * a value argument, followed by a produced value;
|||   * a dependent argument, followed by a produced value.
valCombns : Grammar _ LabelTok True DSALabel
valCombns =  argDepProd     -- :(test)?(rest)!(quest)
         <|> argDep         -- :(test)?(rest)
         <|> argProd        -- :(test)!(quest)
         <|> depProd        -- ?(rest)!(quest)

||| A command with arguments is a command name followed by either:
|||   * a combination of value notations;
|||   * a single value notation (i.e. either: `valArg`, `depVal`, or `prodVal`).
cmdWithArgs : Grammar _ LabelTok True DSALabel
cmdWithArgs = do cn <- cmdName
                 args <- (valCombns <|> valNotation)
                 pure ?cmdWithArgs_rhs

||| A label is either a plain command name, or a command with arguments
label : Grammar _ LabelTok True DSALabel
label =  cmdName
     <|> cmdWithArgs

