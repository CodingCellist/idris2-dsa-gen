module DSAGen.Parser.Common

import public Text.Parser

import Data.String

import Graphics.DOT
import DSAGen.Lexer.Label

%default total

--------------------------------------------------------------------------------
-- GRAMMAR
--------------------------------------------------------------------------------

---------------
-- Terminals --
---------------

export
lParens : Grammar _ LabelTok True ()
lParens = terminal "Expected '('"
            (\case LParens => Just ()
                   _       => Nothing)

export
rParens : Grammar _ LabelTok True ()
rParens = terminal "Expected ')'"
            (\case RParens => Just ()
                   _       => Nothing)

export
addOp : Grammar _ LabelTok True ()
addOp = terminal "Expected '+'"
          (\case AddOp => Just ()
                 _     => Nothing)

||| Whitespace
export
ws : Grammar _ LabelTok True ()
ws = terminal "Expected some whitespace"
        (\case WS => Just ()
               _  => Nothing)

export
comma : Grammar _ LabelTok True ()
comma = terminal "Expected ','"
          (\case Comma => Just ()
                 _     => Nothing)

||| A data constructor
export
dataCons : Grammar _ LabelTok True String
dataCons = terminal "Expected a data constructor"
            (\case DataCons d => Just d
                   _          => Nothing)

