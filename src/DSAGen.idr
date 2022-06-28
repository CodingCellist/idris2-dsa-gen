module DSAGen

import public DSAGen.DSLv2
import public DSAGen.Idris2CodeGen
import DSAGen.Parser

import Graphics.DOT

import System.File
import Text.Lexer.Core

--------------------
-- Util functions --
--------------------

||| Given the name of a graphviz/dot file, attempt to read, parse, and convert
||| its contents to a `DSA`, reporting what went wrong if anything did.
|||
||| @ fileName the name of the file to read
export
dotFileToDSA : HasIO io => (fileName : String) -> io (Either ToDSAError DSAv2)
dotFileToDSA fileName =
  do Right dotAST <- readDOTFile fileName
       | Left err => do printLn err
                        putStrLn "\n"
                        ?dot_error_means_we_cant_proceed
     pure $ toDSAv2 dotAST

--- dotFileToDOTDSA : HasIO io => (fileName : String) -> io (Maybe DOTDSA)
--- dotFileToDOTDSA fileName =
---   do (Right ast) <- readDOTFile fileName
---        | Left err => pure Nothing
---      pure $ toDOTDSA ast

--- ||| Given the name of a graphviz/dot file, attempt to read, parse, and convert
--- ||| its contents to a `DSA`.
--- |||
--- ||| @ fileName the name of the file to read
--- export
--- dotFileToDSA : HasIO io => (fileName : String) -> io (Either String DSA)
--- dotFileToDSA fileName =
---   do (Right ast) <- readDOTFile fileName
---        | Left err => (pure . Left) $ "Couldn't read AST: " ++ show err
---      (Just dotdsa) <- pure $ toDOTDSA ast
---        | Nothing => (pure . Left) "Couldn't convert AST to DOTDSA"
---      (pure . Right) $ toDSA dotdsa

------------------------
-- Tests and examples --
------------------------

successMsg : IO ()
successMsg = putStrLn "\n\n\t -- SUCCESS!!! --\n\n"

||| Test the CG with the DOT-file found in `examples/ATM.gv`.
export
atmTest : IO ()
atmTest =
  do Right atmDSA <- dotFileToDSA "../examples/ATM.gv"
       | Left err => printLn err
     successMsg
     putStrLn $ toIdris2 atmDSA

||| Test the CG with the DOT-file found in `examples/ARQ.gv`.
export
arqTest : IO ()
arqTest =
  do Right arqDSA <- dotFileToDSA "../examples/ARQ.gv"
       | Left err => printLn err
     successMsg
     putStrLn $ toIdris2 arqDSA

||| Test the CG with the DOT-file found in `examples/MESI.gv`
export
mesiTest : IO ()
mesiTest =
  do Right mesiDSA <- dotFileToDSA "../examples/MESI.gv"
       | Left err => printLn err
     putStrLn "\n\n\t -- SUCCESS!!! --\n\n"

||| Test the CG with a user-specified DOT-file.
export
customTest : (gvFile : String) -> IO ()
customTest gvFile =
  do Right customDSA <- dotFileToDSA gvFile
        | Left err => printLn err
     successMsg
     putStrLn $ toIdris2 customDSA

{-
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
-}

