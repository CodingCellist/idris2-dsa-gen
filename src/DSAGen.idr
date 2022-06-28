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
     putStrLn $ toIdris2 mesiDSA

||| Test the CG with a user-specified DOT-file.
export
customTest : (gvFile : String) -> IO ()
customTest gvFile =
  do Right customDSA <- dotFileToDSA gvFile
        | Left err => printLn err
     successMsg
     putStrLn $ toIdris2 customDSA

