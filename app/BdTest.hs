module BdTest
  ( 
    runBdTest
  ) where

import Bidirectional.Simple.Infer
import Bidirectional.Simple.Parser
import Bidirectional.Simple.Pretty

import Data.Text.Prettyprint.Doc

showExpr :: String -> IO ()
showExpr x = do
  putStrLn $ "----------------------------------------------------------"
  putStrLn x
  let e = readExpr x 
  print e
  case infer emptyContext e of
    Right t -> print $ "_ :: " <> pretty t
    Left e -> print $ "ERROR" <+> pretty e

runBdTest :: IO ()
runBdTest = do
  showExpr "if true then (f false) else (h false)"
  showExpr "f :: (Bool -> Bool) -> Bool -> Bool"
  showExpr "f (true :: Bool)"
  showExpr "borked (true :: Bool -> Bool)" -- bad annotation, this should fail
  ------------------
  showExpr "true"
  showExpr "if true then false else true"
