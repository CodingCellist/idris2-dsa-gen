-- Idris2

module DSAGen

import DSAGen.DSL

import Graphics.DOT

import System.File
import Text.Lexer.Core

-- Unsafe generation from the raw DSL to magic strings
atmTest : IO ()
atmTest = do let str = unsafeGenIdris atm
             putStrLn str

dotTest : IO ()
dotTest = do Right ast <- readDOTFile "./ATM_example.gv"
               | Left err => putStrLn "An error occurred."
             putStrLn $ "SUCCESS!!\n" ++ show ast

