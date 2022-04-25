module DSAGen.Label.Parser

import DSAGen.Label.Lexer

import Text.Parser

%default total

---------
-- AST --
---------

||| The type of names that can occur in a label
data Name : Type where
  ||| A data constructor
  DataCons : (dc : String) -> Name
  ||| An Idris name
  IdrName : (n : String) -> Name

data Value : Type where
  MkVal : (dc : Name) -> (args : Maybe $ List1 Name) -> Value

||| The type of actions that can occur in a label
data Action : Type where
  ||| Taking an argument
  |||   ":(val)"
  Take : (val : Value) -> Action

  ||| Depending on a value
  |||   "?(val)"
  Depend : (val : Value) -> Action

  ||| Producing a value
  |||   "!(val)"
  Produce : (val : Value) -> Action

||| A DSALabel either contains a plain command (which is a data constructor), or
||| a command which contains up to 3 actions.
data DSALabel : Type where
  PlainCmd : (cmd : Name) -> DSALabel
  CmdWithActs : (cmd : Name) -> (acts : List1 Action) -> DSALabel


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
dataCons : Grammar _ LabelTok True Name
dataCons = terminal "Expected a data constructor"
            (\case DataCons d => Just (DataCons d)
                   _          => Nothing)

||| A command name is a data constructor
%inline
cmdName : Grammar _ LabelTok True Name
cmdName = dataCons

||| An Idris name
idrName : Grammar _ LabelTok True Name
idrName = terminal "Expected an Idris name"
            (\case IdrName n => Just (IdrName n)
                   _          => Nothing)

-------------------
-- Non-terminals --
-------------------

||| A data constructor which contains arguments (args) must have those args be
||| either data constructors or Idris names, separated by whitespace. There must
||| be at least one argument.
dataArgs : Grammar _ LabelTok True (List1 Name)
dataArgs = some arg
  where
    arg : Grammar _ LabelTok True Name
    arg = do ws
             (idrName <|> dataCons)

||| Argument notation (for any of the edge symbols) is:
|||   A left parens, a result name (optionally taking some valid Idris names as
|||   arguments), and a right parens.
argNotation : Grammar _ LabelTok True Value
argNotation =
  do lParens
     dc <- dataCons
     dArgs <- optional dataArgs
     rParens
     pure (MkVal dc dArgs)

||| Taking a value as an argument is denoted by:
|||   A colon, followed by: a left parens, a result name (optionally taking some
|||   valid Idris names as arguments), and a right parens.
valArg : Grammar _ LabelTok True Action
valArg = do colon
            arg <- argNotation
            pure (Take arg)

||| Depending on a value is denoted by:
|||   A question-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
depVal : Grammar _ LabelTok True Action
depVal = do query
            val <- argNotation
            pure (Depend val)

||| Producing a value as a result is denoted by:
|||   An exclamation-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
prodVal : Grammar _ LabelTok True Action
prodVal = do bang
             val <- argNotation
             pure (Produce val)

-- FIXME: Related to the number of actions (see FIXME further down)
||| A value notation is one of:
|||   * a value argument
|||   * a dependent value
|||   * a produced value
valNotation : Grammar _ LabelTok True (List1 Action)
valNotation =  (valArg  >>= \act => pure $ singleton act)
           <|> (depVal  >>= \act => pure $ singleton act)
           <|> (prodVal >>= \act => pure $ singleton act)


||| A value argument, followed by a dependent value, followed by a produced
||| value.
argDepProd : Grammar _ LabelTok True (List1 Action)
argDepProd = do vArg <- valArg
                dVal <- depVal
                pVal <- prodVal
                pure (vArg ::: [dVal, pVal])

||| A value argument, followed by a dependent value.
argDep : Grammar _ LabelTok True (List1 Action)
argDep = do vArg <- valArg
            dVal <- depVal
            pure (vArg ::: [dVal])

||| A value argument, followed by a produced value.
argProd : Grammar _ LabelTok True (List1 Action)
argProd = do vArg <- valArg
             pVal <- prodVal
             pure (vArg ::: [pVal])

||| A dependent argument, followed by a produced value.
depProd : Grammar _ LabelTok True (List1 Action)
depProd = do dVal <- depVal
             pVal <- prodVal
             pure (dVal ::: [pVal])

-- FIXME: The combination of actions is at most 3 in size; put this in type!

||| The possible value notation combinations are:
|||   * a value argument, followed by a dependent value, followed by a produced
|||     value;
|||   * a value argument, followed by a dependent value;
|||   * a value argument, followed by a produced value;
|||   * a dependent argument, followed by a produced value.
valCombns : Grammar _ LabelTok True (List1 Action)
valCombns =  argDepProd     -- :(test)?(rest)!(quest)
         <|> argDep         -- :(test)?(rest)
         <|> argProd        -- :(test)!(quest)
         <|> depProd        -- ?(rest)!(quest)

||| A command with arguments is a command name followed by either:
|||   * a combination of value notations;
|||   * a single value notation (i.e. either: `valArg`, `depVal`, or `prodVal`).
cmdWithArgs : Grammar _ LabelTok True DSALabel
cmdWithArgs = do cn <- cmdName
                 acts <- (valCombns <|> valNotation)
                 pure (CmdWithActs cn acts)

||| A label is either a plain command name, or a command with arguments
label : Grammar _ LabelTok True DSALabel
label =  (cmdName >>= \cn => pure (PlainCmd cn))
     <|> cmdWithArgs

