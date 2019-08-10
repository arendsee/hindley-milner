module DkTest
  ( 
    runDkTest
  ) where

import Bidirectional.Dunfield.Infer
import Bidirectional.Dunfield.Parser
import Bidirectional.Dunfield.Data (runStack)

import Data.Text.Prettyprint.Doc

showExpr :: Bool -> String -> IO ()
showExpr verbose x = do
  putStrLn $ "----------------------------------------------------------"
  putStrLn x
  let e = readExpr x 
  if verbose
  then print e
  else return ()
  x <- runStack (infer [] e) verbose
  case x of
    Right (_, t) -> print $ "_ :: " <> pretty t
    Left err -> print $ "ERROR" <+> pretty err
  putStr "\n"

runDkTest :: IO ()
runDkTest = do
  -- primitives
  showExpr False "42"
  showExpr False "True"
  showExpr False "4.2"
  showExpr False "\"this is a string literal\""
  -- simple functions
  showExpr False "(\\x -> True)"
  showExpr False "(\\x -> True) 42"
  showExpr False "(\\x -> (\\y -> True) x) 42"  -- expect: Bool
  showExpr False "(\\x -> (\\y -> x) True) 42"  -- expect: Int
  showExpr False "(\\x y->x) 1 True"
  showExpr False "(\\x y -> x) :: forall a b . a -> b -> a"
  showExpr False "((\\x -> x) :: forall a . a -> a) True"
  showExpr False "((\\x y -> x) :: forall a b . a -> b -> a) True"
  showExpr False "x = True; 4.2"
  showExpr False "x = True; (\\y -> y) x"
  showExpr True "f = (\\x y -> x); f 42"
