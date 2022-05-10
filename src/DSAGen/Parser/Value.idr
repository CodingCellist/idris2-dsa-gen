module DSAGen.Parser.Value

import Graphics.DOT
import DSAGen.Lexer.Common
import DSAGen.Parser.Common

import Data.List1
import Data.String

%default total

--------------------------------------------------------------------------------
-- AST
--------------------------------------------------------------------------------

||| The kind of values that can occur in a DSA
public export
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


--------------------------------------------------------------------------------
-- INTERFACES
--------------------------------------------------------------------------------

----------
-- Show --
----------

export
covering
Show Value where
  show (IdrName n) = "(IdrName " ++ n ++ ")"
  show (LitVal lit) = "(LitVal " ++ show lit ++ ")"
  show (DataVal dc Nothing) = "(DataVal " ++ dc ++ ")"
  show (DataVal dc (Just args)) =
    "(DataVal " ++ dc ++ " " ++ joinBy " " (toList $ map show args)
  show (AddExpr num addend) =
    "(AddExpr " ++ joinBy " " [show num, show addend] ++ ")"
  show (Tuple fst snd) = "(Tuple " ++ joinBy " " [show fst, show snd] ++ ")"

---------
-- DOT --
---------

||| Convert the given `Value` to its DOT/GraphViz string representation.
||| DIFFERENT FROM `show`!
export
covering
valToDOTString : Value -> String
valToDOTString (IdrName n) = n
valToDOTString (LitVal lit) = show lit
valToDOTString (DataVal dc Nothing) = dc
valToDOTString (DataVal dc (Just args)) =
  dc ++ " " ++ (joinBy " " (toList $ map valToDOTString args))
valToDOTString (AddExpr num addend) =
  "(" ++ (valToDOTString num) ++ " + " ++ (valToDOTString addend) ++ ")"
valToDOTString (Tuple fst snd) =
  "(" ++ (valToDOTString fst) ++ "," ++ (valToDOTString snd) ++ ")"

export
covering
DOTDOTID Value where
  toDOTID val = StringID (valToDOTString val)

--------------------------------------------------------------------------------
-- GRAMMAR
--------------------------------------------------------------------------------

---------------
-- Terminals --
---------------

||| An Idris name
export
idrName : Grammar _ LabelTok True Value
idrName = terminal "Expected an Idris name"
            (\case IdrName n => Just (IdrName n)
                   _         => Nothing)

||| A number literal
export
numLit : Grammar _ LabelTok True Value
numLit = terminal "Expected a number literal"
            (\case NumLit l => Just (LitVal !(parseInteger l))
                   _        => Nothing)

-------------------
-- Non-terminals --
-------------------

------------
-- Values --
------------

mutual
  ||| A value can be one of: a data constructor, an addition expression, an Idris
  ||| name, or a literal number.
  export
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
  export
  dcArg : Grammar _ LabelTok True Value
  dcArg = do ws
             -- option () lParens
             arg <- value
             -- option () rParens
             pure arg

  ||| Some arguments to a data constructor.
  export
  dcArgs : Grammar _ LabelTok True (List1 Value)
  dcArgs = do arg <- dcArg
              args <- many dcArg
              pure (arg ::: args)

  ||| A data constructor which contains some arguments.
  export
  argsDataVal : Grammar _ LabelTok True Value
  argsDataVal = do -- option () lParens
                   dc <- dataCons
                   args <- dcArgs
                   -- option () rParens
                   pure (DataVal dc (Just args))

  ||| A data constructor which does not contain any arguments.
  export
  plainDataVal : Grammar _ LabelTok True Value
  plainDataVal = do dc <- dataCons
                    pure (DataVal dc Nothing)

  ||| Addition is a left parenthesis, followed by: a name or a literal, some
  ||| whitespace, a plus, some whitespace, another name or identifier, and
  ||| finally a right parenthesis.
  export
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
  export
  tupleExpr : Grammar _ LabelTok True Value
  tupleExpr = do lParens
                 fst <- value
                 option () ws
                 comma
                 option () ws
                 snd <- value
                 pure (Tuple fst snd)


