module DkTest
  ( 
    runDkTest
  ) where

import Bidirectional.Dunfield.Infer
import Bidirectional.Dunfield.Parser
import Bidirectional.Dunfield.Data (runStack)

import Data.Text.Prettyprint.Doc

showExpr :: String -> IO ()
showExpr x = do
  putStrLn $ "----------------------------------------------------------"
  putStrLn x
  let e = readExpr x 
  print e
  x <- runStack (infer [] e)
  case x of
    Right (_, t) -> print $ "_ :: " <> pretty t
    Left err -> print $ "ERROR" <+> pretty err
  putStr "\n"

runDkTest :: IO ()
runDkTest = do
  showExpr "(\\x -> x) UNIT"
