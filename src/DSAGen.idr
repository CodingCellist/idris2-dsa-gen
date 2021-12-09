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

||| But sire, our troops!
export
goForGold : IO ()
goForGold =
  do Right ast <- readDOTFile "./ATM_example.gv"
        | Left err => putStrLn "Couldn't get AST."
     putStrLn "Got AST:"
     putStrLn $ show ast
     (Just dotDSA) <- pure $ toDOTDSA ast
        | Nothing => putStrLn "AST was not a DOTDSA."
     let dsa = toDSA dotDSA
     putStrLn ""
     putStrLn "Ĥ̷̤E̶̘̐ ̵̟͒C̴̝̐O̵͒ͅM̴͝ͅE̴̺̚S̷̹̃"
     putStrLn ""
     putStrLn $ unsafeGenIdris dsa

export
fullATMTest : IO ()
fullATMTest =
  do Right ast <- readDOTFile "./ATM_example.gv"
        | Left err => putStrLn "Couldn't get AST."
     (Just dotDSA) <- pure $ toDOTDSA ast
        | Nothing => putStrLn "AST was not a DOTDSA."
     let dsa = toDSA dotDSA
     putStrLn $ unsafeGenIdris dsa

