-- Idris2

module DSAGen

import DSAGen.DSL

import System.File
import Text.Lexer.Core

atmTest : IO ()
atmTest = do let str = unsafeGenIdris atm
             putStrLn str

