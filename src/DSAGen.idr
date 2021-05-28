-- Idris2

module DSAGen

import DSAGen.DSL
import DSAGen.DOTLex

import System.File
import Text.Lexer.Core

debugLex : (fp : String) -> IO ()
debugLex fp = do Right contents <- readFile fp
                   | Left err => putStrLn $ show err
                 let (tokList, (line, col, rem)) = lex contents
                 putStrLn $ "Reached " ++ (show line) ++ ":" ++ (show col)
                 putStrLn $ "Remainder: " ++ rem
                 putStrLn "TOKEN LIST"
                 putStrLn $ show tokList

atmTest : IO ()
atmTest = do let str = unsafeGenIdris atm
             putStrLn str

