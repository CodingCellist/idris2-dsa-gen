module DSAGen.Parser.Label

import Graphics.DOT

import DSAGen.Lexer.Common
import DSAGen.Parser.Common
import DSAGen.Parser.Value

import Data.List1
import Data.String

%default total

--------------------------------------------------------------------------------
-- AST
--------------------------------------------------------------------------------

||| Taking an argument
|||   ":(val)"
public export
data TakeArg : Type where
  Takes : (val : Value) -> TakeArg

||| Depending on a value
|||   "?(val)"
public export
data DepArg : Type where
  DepsOn : (val : Value) -> DepArg

||| Producing a value
|||   "!(val)"
public export
data ProdArg : Type where
  Produce : (val : Value) -> ProdArg

||| A DSALabel either contains a plain command (which is a data constructor), or
||| a command which contains up to 3 actions.
public export
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


--------------------------------------------------------------------------------
-- INTERFACES
--------------------------------------------------------------------------------

---------
-- DOT --
---------

export
covering
DOTAssign DSALabel where
  -- MkAssign (NameID "label") rhs
  toAssign dsaLabel =
     let label = MkAssign (NameID "label")
     in case dsaLabel of
             (PlainCmd cmd) =>
                label (StringID cmd)
             (TakeCmd cmd (Takes val)) =>
                label (StringID $ cmd ++ ":(" ++ valToDOTString val ++ ")")
             (DepCmd cmd (DepsOn val)) =>
                label (StringID $ cmd ++ "?(" ++ valToDOTString val ++ ")")
             (ProdCmd cmd (Produce val)) =>
                label (StringID $ cmd ++ "!(" ++ valToDOTString val ++ ")")
             (TDCmd cmd (Takes argVal) (DepsOn depVal)) =>
                let argStr = ":(" ++ valToDOTString argVal ++ ")"
                    depStr = "?(" ++ valToDOTString depVal ++ ")"
                in label (StringID $ cmd ++ argStr ++ depStr)
             (TPCmd cmd (Takes argVal) (Produce prodVal)) =>
                let argStr = ":(" ++ valToDOTString argVal ++ ")"
                    prodStr = "!(" ++ valToDOTString prodVal ++ ")"
                in label (StringID $ cmd ++ argStr ++ prodStr)
             (DPCmd cmd (DepsOn depVal) (Produce prodVal)) =>
                let depStr = "?(" ++ valToDOTString depVal ++ ")"
                    prodStr = "!(" ++ valToDOTString prodVal ++ ")"
                in label (StringID $ cmd ++ depStr ++ prodStr)
             (TDPCmd cmd (Takes argVal) (DepsOn depVal) (Produce prodVal)) =>
                let argStr = ":(" ++ valToDOTString argVal ++ ")"
                    depStr = "?(" ++ valToDOTString depVal ++ ")"
                    prodStr = "!(" ++ valToDOTString prodVal ++ ")"
                in label (StringID $ cmd ++ argStr ++ depStr ++ prodStr)

||| Converting a `List1 DSALabel` to a DOTAssign converts each of the
||| `DSALabel`s to their `DOTAssign` representations, and then combines each of
||| the string representations in the assignments using semicolons (';') as this
||| is how multiple commands are written in a single label in DOT.
export
covering
DOTAssign (List1 DSALabel) where
  toAssign dsaLabels = combineStringIDsBy ";" (map toAssign dsaLabels)
    where
      getRHS : Assign -> String
      getRHS (MkAssign _ (StringID str)) = str
      getRHS _ = assert_total $ idris_crash "Tried to convert a non-StringID to a DOTAssign"

      combineStringIDsBy : (sep : String) -> (stringIDs : List1 Assign) -> Assign
      combineStringIDsBy sep stringIDs =
        let combined = joinBy sep (toList $ map getRHS stringIDs)
        in MkAssign (NameID "label") (StringID combined)

--------
-- Eq --
--------

export
covering
Eq TakeArg where
  (==) (Takes arg1) (Takes arg2) = arg1 == arg2

export
covering
Eq DepArg where
  (==) (DepsOn dep1) (DepsOn dep2) = dep1 == dep2

export
covering
Eq ProdArg where
  (==) (Produce val1) (Produce val2) = val1 == val2

export
covering
Eq DSALabel where
  (==) (PlainCmd cmd1) (PlainCmd cmd2) = cmd1 == cmd2

  (==) (TakeCmd cmd1 arg1) (TakeCmd cmd2 arg2) =
    cmd1 == cmd2 && arg1 == arg2

  (==) (DepCmd cmd1 dep1) (DepCmd cmd2 dep2) =
    cmd1 == cmd2 && dep1 == dep2

  (==) (ProdCmd cmd1 res1) (ProdCmd cmd2 res2) =
    cmd1 == cmd2 && res1 == res2

  (==) (TDCmd cmd1 arg1 dep1) (TDCmd cmd2 arg2 dep2) =
    cmd1 == cmd2 && arg1 == arg2 && dep1 == dep2

  (==) (TPCmd cmd1 arg1 res1) (TPCmd cmd2 arg2 res2) =
    cmd1 == cmd2 && arg1 == arg2 && res1 == res2

  (==) (DPCmd cmd1 dep1 res1) (DPCmd cmd2 dep2 res2) =
    cmd1 == cmd2 && dep1 == dep2 && res1 == res2

  (==) (TDPCmd cmd1 arg1 dep1 res1) (TDPCmd cmd2 arg2 dep2 res2) =
    cmd1 == cmd2 && arg1 == arg2 && dep1 == dep2 && res1 == res2

  (==) _ _ = False


----------
-- Show --
----------

export
covering
Show TakeArg where
  show (Takes arg) = "(Takes " ++ show arg ++ ")"

export
covering
Show DepArg where
  show (DepsOn val) = "(DepsOn " ++ show val ++ ")"

export
covering
Show ProdArg where
  show (Produce val) = "(Produce " ++ show val ++ ")"

export
covering
Show DSALabel where
  show (PlainCmd cmd) = "(PlainCmd '\{cmd}')"
  show (TakeCmd cmd arg) = "(TakeCmd '\{cmd}' \{show arg})"
  show (DepCmd cmd dep) = "(DepCmd '\{cmd}' \{show dep})"
  show (ProdCmd cmd res) = "(ProdCmd '\{cmd}' \{show res})"
  show (TDCmd cmd arg dep) = "(TDCmd '\{cmd}' \{show arg} \{show dep})"
  show (TPCmd cmd arg res) = "(TPCmd '\{cmd}' \{show arg} \{show res})"
  show (DPCmd cmd dep res) = "(DPCmd '\{cmd}' \{show dep} \{show res})"
  show (TDPCmd cmd arg dep res) = "(TDPCmd '\{cmd}' \{show arg} \{show dep} \{show res})"


--------------------------------------------------------------------------------
-- GRAMMAR
--------------------------------------------------------------------------------

---------------
-- Terminals --
---------------

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

||| A command name is a data constructor
%inline
cmdName : Grammar _ LabelTok True String
cmdName = dataCons

-------------------
-- Non-terminals --
-------------------

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


--------------------------------------------------------------------------------
-- LABEL PARSER
--------------------------------------------------------------------------------

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
parseLabel :  (toks :List (WithBounds LabelTok))
           -> Either (List1 (ParsingError LabelTok))
                     (ParsingWarnings, DSALabel, List (WithBounds LabelTok))
parseLabel toks = parse label toks

