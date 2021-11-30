module DSAGen

import DSAGen.DSL
import DSAGen.DOTDSA

import Graphics.DOT

import System.File
import Text.Lexer.Core

-- Unsafe generation from the raw DSL to magic strings
atmTest : IO ()
atmTest = do let str = unsafeGenIdris atm
             putStrLn str

export
dotTest : IO ()
dotTest = do Right ast <- readDOTFile "./ATM_example.gv"
               | Left err => putStrLn "Couldn't get AST."
             putStrLn $ "SUCCESS!!\n" ++ show ast

export
dotDSATest : IO ()
dotDSATest = do Right ast <- readDOTFile "./ATM_example.gv"
                  | Left err => putStrLn "Couldn't get AST."
                putStrLn "Got AST:"
                putStrLn $ show ast
                putStrLn "-- CONVERTING --"
                case toDOTDSA ast of
                     Nothing => putStrLn "AST is not a DOTDSA."
                     (Just dotDSA) =>
                        do putStrLn "SUCCESS!!!"
                           putStrLn $ show $ toDOT dotDSA

