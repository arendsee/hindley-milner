module DkTest
  ( 
    runDkTest
  ) where

import Bidirectional.Dunfield.Infer
import Bidirectional.Dunfield.Parser
import Bidirectional.Dunfield.Data (runStack)

import Data.Text.Prettyprint.Doc

showExpr :: Int -> String -> IO ()
showExpr verbosity x = do
  log0 verbosity
  let e = readExpr x 
  log1 verbosity e
  x <- runStack (typecheck e) verbosity
  log2 verbosity x
  where
    log0 0 = putStrLn x
    log0 1 = do
      putStrLn $ "----------------------------------------------------------"
      putStrLn x
    log1 0 _ = return ()
    log1 1 e' = print e'
    log2 _ (Right t) = print $ "_ :: " <> pretty t
    log2 _ (Left err) = print $ "ERROR" <+> pretty err
    log3 _ _ = "\n"

runDkTest :: IO ()
runDkTest = do
  -- primitives
  showExpr 0 "42"
  showExpr 0 "True"
  showExpr 0 "4.2"
  showExpr 0 "\"this is a string literal\""
  -- simple functions
  showExpr 0 "(\\x -> True)"
  showExpr 0 "(\\x -> True) 42"
  showExpr 0 "(\\x -> (\\y -> True) x) 42"  -- expect: Bool
  showExpr 0 "(\\x -> (\\y -> x) True) 42"  -- expect: Int
  showExpr 0 "(\\x y->x) 1 True"
  showExpr 0 "(\\x y -> x) :: forall a b . a -> b -> a"
  showExpr 0 "((\\x -> x) :: forall a . a -> a) True"
  showExpr 0 "((\\x y -> x) :: forall a b . a -> b -> a) True"
  showExpr 0 "x = True; 4.2"
  showExpr 0 "x = True; (\\y -> y) x"
  -- should be the same
  showExpr 0 "f = (\\x y -> x); f 42"
  showExpr 0 "f = (\\x y -> x); x = f 42; x"
  -- showExpr 0 "f = (\\x -> y); f :: forall a . a -> a; f 42"
  showExpr 0 "x :: Int"
  showExpr 0 "xs :: List a"
  showExpr 0 "f :: forall a . a -> a; f 42"
  showExpr 0 "apply :: forall a b . (a->b) -> a -> b; f :: Int -> Bool; apply f 42"
