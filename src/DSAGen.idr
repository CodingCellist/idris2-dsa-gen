module DSAGen

import public DSAGen.DSL
import public DSAGen.DOTDSA

import Graphics.DOT

import System.File
import Text.Lexer.Core

--------------------
-- Util functions --
--------------------

||| Given the name of a graphviz/dot fiel, attempt to read, parse, and convert
||| its contents to a `DOTDSA`.
|||
||| @ fileName the name of the file to read
dotFileToDOTDSA : HasIO io => (fileName : String) -> io (Maybe DOTDSA)
dotFileToDOTDSA fileName =
  do (Right ast) <- readDOTFile fileName
       | Left err => pure Nothing
     pure $ toDOTDSA ast

||| Given the name of a graphviz/dot file, attempt to read, parse, and convert
||| its contents to a `DSA`.
|||
||| @ fileName the name of the file to read
export
dotFileToDSA : HasIO io => (fileName : String) -> io (Either String DSA)
dotFileToDSA fileName =
  do (Right ast) <- readDOTFile fileName
       | Left err => (pure . Left) $ "Couldn't read AST: " ++ show err
     (Just dotdsa) <- pure $ toDOTDSA ast
       | Nothing => (pure . Left) "Couldn't convert AST to DOTDSA"
     (pure . Right) $ toDSA dotdsa

------------------------
-- Tests and examples --
------------------------

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
                           putStrLn $ show $ toGraph dotDSA

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

