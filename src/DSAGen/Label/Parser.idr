module DSAGen.Label.Parser

import DSAGen.Label.Lexer

import Text.Parser
import Data.String

%default total

---------
-- AST --
---------

data Value : Type where
  ||| A data constructor, potentially taking some arguments
  DataVal : (dc : String) -> (args : Maybe $ List1 Value) -> Value
  ||| An Idris name
  IdrName : (n : String) -> Value
  ||| A literal number
  LitVal  : (lit : Integer) -> Value

||| The type of expressions that can occur in a label
data LExpr : Type where
  AddExpr : (num : Value) -> (addend : Value) -> LExpr

||| Taking an argument
|||   ":(val)"
data TakeArg : Type where
  Takes : (val : Value) -> TakeArg

||| Depending on a value
|||   "?(val)"
data DepArg : Type where
  DepOn : (val : Value) -> DepArg

||| Producing a value
|||   "!(val)"
data ProdArg : Type where
  Produce : (val : Value) -> Action

||| A DSALabel either contains a plain command (which is a data constructor), or
||| a command which contains up to 3 actions.
data DSALabel : Type where
  ||| A command without any arguments
  PlainCmd : (cmd : Value) -> DSALabel
  ||| A command taking an argument
  TakeCmd : (cmd : Value) -> (arg : TakeArg) -> DSALabel
  ||| A command depending on a value
  DepCmd : (cmd : Value) -> (dep : DepArg) -> DSALabel
  ||| A command producing a value
  ProdCmd : (cmd : Value) -> (res : ProdArg) -> DSALabel
  ||| A command taking an argument and depending on a value
  TDCmd : (cmd : Value) -> (arg : TakeArg) -> (dep : DepArg) -> DSALabel
  ||| A command taking an argument and producing a value
  TPCmd : (cmd : Value) -> (arg : TakeArg) -> (res : ProdArg) -> DSALabel
  ||| A command depending on a value and producing a value
  DPCmd : (cmd : Value) -> (dep : DepArg) -> (res : ProdArg) -> DSALabel
  ||| A command taking an argument, depending on a value, and producing a value
  TDPCmd :  (cmd : Value)
         -> (arg : TakeArg)
         -> (dep : DepArg)
         -> (res : ProdArg)
         -> DSALabel


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
dataCons : Grammar _ LabelTok True String
dataCons = terminal "Expected a data constructor"
            (\case DataCons d => Just d
                   _          => Nothing)

||| A command name is a data constructor
%inline
cmdName : Grammar _ LabelTok True String
cmdName = dataCons

||| An Idris name
idrName : Grammar _ LabelTok True String
idrName = terminal "Expected an Idris name"
            (\case IdrName n => Just n
                   _         => Nothing)

||| A number literal
numLit : Grammar _ LabelTok True Value
numLit = terminal "Expected a number literal"
            (\case NumLit l => Just (LitVal !(parseInteger l))
                   _        => Nothing)

-------------------
-- Non-terminals --
-------------------

||| Addition is a name or a literal, followed by a plus, followed by another
||| name or identifier.
addExpr : Grammar _ LabelTok True LExpr
addExpr = ?addExpr_rhs

||| A data constructor which contains arguments (args) must have those args be
||| either data constructors or Idris names, separated by whitespace. There must
||| be at least one argument.
dataArgs : Grammar _ LabelTok True (List1 Value)
dataArgs = some (dcNestedArg <|> parensNameArg <|> dcArg <|> nameArg)
  where
    dcNestedArg : Grammar _ LabelTok True Value
    dcNestedArg = do ws
                     lParens
                     dc <- dataCons
                     dcArgs <- optional dataArgs
                     rParens
                     pure (DataVal dc dcArgs)


    parensNameArg : Grammar _ LabelTok True Value
    parensNameArg = do ws
                       lParens
                       n <- idrName
                       rParens
                       pure (IdrName n)

    dcArg : Grammar _ LabelTok True Value
    dcArg = do ws
               dc <- dataCons
               dcArgs <- optional dataArgs
               pure (DataVal dc dcArgs)

    nameArg : Grammar _ LabelTok True Value
    nameArg = do ws
                 n <- idrName
                 pure (IdrName n)

||| Argument notation (for any of the edge symbols) is:
|||   A left parens, a result name (optionally taking some valid Idris names as
|||   arguments), and a right parens.
argNotation : Grammar _ LabelTok True Value
argNotation =
  do lParens
     dc <- dataCons
     dArgs <- optional dataArgs
     rParens
     pure (DataVal dc dArgs)

||| Taking a value as an argument is denoted by:
|||   A colon, followed by: a left parens, a result name (optionally taking some
|||   valid Idris names as arguments), and a right parens.
valArg : Grammar _ LabelTok True Action
valArg = do colon
            commit
            arg <- argNotation
            pure (Take arg)

||| Depending on a value is denoted by:
|||   A question-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
depVal : Grammar _ LabelTok True Action
depVal = do query
            commit
            val <- argNotation
            pure (Depend val)

||| Producing a value as a result is denoted by:
|||   An exclamation-mark, followed by: a left parens, a result name (optionally
|||   taking some valid Idris names as arguments), and a right parens.
prodVal : Grammar _ LabelTok True Action
prodVal = do bang
             commit
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
                 pure (CmdWithActs (DataVal cn Nothing) acts)

||| A label is either a plain command name, or a command with arguments
label : Grammar _ LabelTok True DSALabel
label =  cmdWithArgs
     <|> (cmdName >>= \cn => pure (PlainCmd (DataVal cn Nothing)))

export
parse :  List (WithBounds LabelTok)
      -> Either (List1 (ParsingError LabelTok)) (DSALabel, List (WithBounds LabelTok))
parse toks = parse label toks

