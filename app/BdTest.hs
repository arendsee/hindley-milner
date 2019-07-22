module BdTest
  ( 
    runBdTest
  ) where

import BD.Infer
import BD.Parser

showExpr :: String -> IO ()
showExpr x = do
  putStrLn $ "----------------------------------------------------------"
  putStrLn x
  let e = readExpr x 
  print $ e
  print $ infer emptyContext e

runBdTest :: IO ()
runBdTest = do
  showExpr "if true then (f false) else (h false)"
  showExpr "f :: (Bool -> Bool) -> Bool -> Bool"
  showExpr "f (true :: Bool)"
  showExpr "borked (true :: Bool -> Bool)" -- bad annotation, this should fail
  ------------------
  showExpr "true"
  showExpr "if true then false else true"
