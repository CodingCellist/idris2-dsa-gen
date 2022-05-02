module DSAGen.Label.Parser

import DSAGen.Label.Lexer

import Text.Parser
import Data.String

%default total

---------
-- AST --
---------

data Value : Type where
  -- "base cases"
  ||| An Idris name
  IdrName : (n : String) -> Value
  ||| A literal number
  LitVal  : (lit : Integer) -> Value

  -- recursive structures
  ||| A data constructor, potentially taking some arguments
  DataVal : (dc : String) -> (args : Maybe $ List1 Value) -> Value
  ||| An addition expression
  AddExpr : (num : Value) -> (addend : Value) -> Value
  ||| A tuple expression
  Tuple : (fst : Value) -> (snd : Value) -> Value

||| Taking an argument
|||   ":(val)"
data TakeArg : Type where
  Takes : (val : Value) -> TakeArg

||| Depending on a value
|||   "?(val)"
data DepArg : Type where
  DepsOn : (val : Value) -> DepArg

||| Producing a value
|||   "!(val)"
data ProdArg : Type where
  Produce : (val : Value) -> ProdArg

||| A DSALabel either contains a plain command (which is a data constructor), or
||| a command which contains up to 3 actions.
data DSALabel : Type where
  ||| A command without any arguments
  PlainCmd : (cmd : String) -> DSALabel
  ||| A command taking an argument
  TakeCmd : (cmd : String) -> (arg : TakeArg) -> DSALabel
  ||| A command depending on a value
  DepCmd : (cmd : String) -> (dep : DepArg) -> DSALabel
  ||| A command producing a value
  ProdCmd : (cmd : String) -> (res : ProdArg) -> DSALabel
  ||| A command taking an argument and depending on a value
  TDCmd : (cmd : String) -> (arg : TakeArg) -> (dep : DepArg) -> DSALabel
  ||| A command taking an argument and producing a value
  TPCmd : (cmd : String) -> (arg : TakeArg) -> (res : ProdArg) -> DSALabel
  ||| A command depending on a value and producing a value
  DPCmd : (cmd : String) -> (dep : DepArg) -> (res : ProdArg) -> DSALabel
  ||| A command taking an argument, depending on a value, and producing a value
  TDPCmd :  (cmd : String)
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

comma : Grammar _ LabelTok True ()
comma = terminal "Expected ','"
          (\case Comma => Just ()
                 _     => Nothing)

addOp : Grammar _ LabelTok True ()
addOp = terminal "Expected '+'"
          (\case AddOp => Just ()
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
idrName : Grammar _ LabelTok True Value
idrName = terminal "Expected an Idris name"
            (\case IdrName n => Just (IdrName n)
                   _         => Nothing)

||| A number literal
numLit : Grammar _ LabelTok True Value
numLit = terminal "Expected a number literal"
            (\case NumLit l => Just (LitVal !(parseInteger l))
                   _        => Nothing)


--------------------------------------------------------------------------------
-- NON-TERMINALS
--------------------------------------------------------------------------------

------------
-- Values --
------------

mutual
  ||| A value can be one of: a data constructor, an addition expression, an Idris
  ||| name, or a literal number.
  %inline
  value : Grammar _ LabelTok True Value
  value =  argsDataVal
       <|> addExpr
       <|> tupleExpr
       <|> plainDataVal
       <|> idrName
       <|> numLit

  ||| An argument to a data constructor must be preceded by whitespace
  ||| ~~and can optionally be inside parentheses~~.
  dcArg : Grammar _ LabelTok True Value
  dcArg = do ws
             -- option () lParens
             arg <- value
             -- option () rParens
             pure arg

  ||| Some arguments to a data constructor.
  dcArgs : Grammar _ LabelTok True (List1 Value)
  dcArgs = do arg <- dcArg
              args <- many dcArg
              pure (arg ::: args)

  ||| A data constructor which contains some arguments.
  argsDataVal : Grammar _ LabelTok True Value
  argsDataVal = do -- option () lParens
                   dc <- dataCons
                   args <- dcArgs
                   -- option () rParens
                   pure (DataVal dc (Just args))

  ||| A data constructor which does not contain any arguments.
  plainDataVal : Grammar _ LabelTok True Value
  plainDataVal = do dc <- dataCons
                    pure (DataVal dc Nothing)

  ||| Addition is a left parenthesis, followed by: a name or a literal, some
  ||| whitespace, a plus, some whitespace, another name or identifier, and
  ||| finally a right parenthesis.
  addExpr : Grammar _ LabelTok True Value
  addExpr = do lParens
               lhs <- (idrName <|> numLit)
               ws
               addOp
               ws
               rhs <- (idrName <|> numLit)
               rParens
               pure $ AddExpr lhs rhs

  ||| Tuples are a left parenthesis, followed by: a first value, a comma, a
  ||| second value, and finally a right parenthesis.
  ||| There may be whitespace inbetween the values and theh comma.
  tupleExpr : Grammar _ LabelTok True Value
  tupleExpr = do lParens
                 fst <- value
                 option () ws
                 comma
                 option () ws
                 snd <- value
                 pure (Tuple fst snd)

--------------------
-- Edge notations --
--------------------

||| The notation for taking an argument is a colon, followed by: a left parens,
||| the value to take, and a right parens.
takeArg : Grammar _ LabelTok True TakeArg
takeArg = do colon
             -- commit
             lParens
             arg <- value
             rParens
             pure (Takes arg)

||| The notation for depending on a value is a query/question-mark, followed by:
||| a left parens, the value to depend on, and a right parens.
depArg : Grammar _ LabelTok True DepArg
depArg = do query
            -- commit
            lParens
            arg <- value
            rParens
            pure (DepsOn arg)

||| The notation for producing/returning a value is a bang/exclamation-mark,
||| followed by: a left parens, the value to produce, and a right parens.
prodArg : Grammar _ LabelTok True ProdArg
prodArg = do bang
             -- commit
             lParens
             val <- value
             rParens
             pure (Produce val)

--------------
-- Commands --
--------------

||| A plain command is a data constructor without any arguments and having no
||| edge statements (i.e. neither taking, depending on, or producing any
||| values).
plainCmd : Grammar _ LabelTok True DSALabel
plainCmd = do cmd <- cmdName
              pure (PlainCmd cmd)

||| A command taking a value as an argument.
takeCmd : Grammar _ LabelTok True DSALabel
takeCmd = do cmd <- cmdName
             arg <- takeArg
             pure (TakeCmd cmd arg)

||| A command depending on a value.
depCmd : Grammar _ LabelTok True DSALabel
depCmd = do cmd <- cmdName
            deps <- depArg
            pure (DepCmd cmd deps)

||| A command producing a value as a result.
prodCmd : Grammar _ LabelTok True DSALabel
prodCmd = do cmd <- cmdName
             res <- prodArg
             pure (ProdCmd cmd res)

||| A command taking an argument and depending on a value.
tdCmd : Grammar _ LabelTok True DSALabel
tdCmd = do cmd <- cmdName
           arg <- takeArg
           deps <- depArg
           pure (TDCmd cmd arg deps)

||| A command taking an argument and producing a value.
tpCmd : Grammar _ LabelTok True DSALabel
tpCmd = do cmd <- cmdName
           arg <- takeArg
           val <- prodArg
           pure (TPCmd cmd arg val)

||| A command depending on a value and producing a value.
dpCmd : Grammar _ LabelTok True DSALabel
dpCmd = do cmd <- cmdName
           deps <- depArg
           val <- prodArg
           pure (DPCmd cmd deps val)

||| A command taking an argument, depending on a value, and producing a value.
tdpCmd : Grammar _ LabelTok True DSALabel
tdpCmd = do cmd <- cmdName
            arg <- takeArg
            deps <- depArg
            val <- prodArg
            pure (TDPCmd cmd arg deps val)

----------------
-- The parser --
----------------

label : Grammar _ LabelTok True DSALabel
label =  tdpCmd
     <|> dpCmd
     <|> tpCmd
     <|> tdCmd
     <|> prodCmd
     <|> depCmd
     <|> takeCmd
     <|> plainCmd

||| Parse a label containing a DSA command
export
parse :  List (WithBounds LabelTok)
      -> Either (List1 (ParsingError LabelTok)) (DSALabel, List (WithBounds LabelTok))
parse toks = parse label toks

