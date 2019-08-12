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
    log0 0 = return ()
    log0 1 = putStrLn x
    log0 2 = do
      putStrLn $ "----------------------------------------------------------"
      putStrLn x
    log1 v e'
      | v < 2 = return ()
      | v == 2 = print e'
    log2 v (Right t)
      | v > 0 = print $ "_ :: " <> pretty t
      | otherwise = return ()
    log2 v (Left err)
      | v > 0 = print $ "ERROR" <+> pretty err
      | otherwise = return ()
    log3 v _
      | v > 0 = "\n"
      | otherwise = return ()

runDkTest :: IO ()
runDkTest = do
  showExpr 0 "42"
  showExpr 0 "True"
  showExpr 0 "4.2"
  showExpr 0 "\"this is a string literal\""
  showExpr 0 "(\\x -> True)"
  showExpr 0 "(\\x -> True) 42"
  showExpr 0 "(\\x -> (\\y -> True) x) 42"
  showExpr 0 "(\\x -> (\\y -> x) True) 42"
  showExpr 0 "(\\x y->x) 1 True"
  showExpr 0 "(\\x y -> x) :: forall a b . a -> b -> a"
  showExpr 0 "((\\x -> x) :: forall a . a -> a) True"
  showExpr 0 "((\\x y -> x) :: forall a b . a -> b -> a) True"
  showExpr 0 "x = True; 4.2"
  showExpr 0 "x = True; (\\y -> y) x"
  showExpr 0 "f = (\\x y -> x); f 42"
  showExpr 0 "f = (\\x y -> x); x = f 42; x"
  showExpr 0 "x :: Int"
  showExpr 0 "xs :: List a"
  showExpr 0 "f :: forall a . a -> a; f 42"
  showExpr 0 "apply :: forall a b . (a->b) -> a -> b; f :: Int -> Bool; apply f 42"
  showExpr 0 "[1,2,3]"
  showExpr 0 "[]"
  -- showExpr 1 "[1,2,True]" -- TODO: Add better error message
  showExpr 0 "f :: [Int] -> Bool; f [1]"
  showExpr 0 "f :: forall a . [a] -> Bool; f [1]"
  showExpr 0 "map :: forall a b . (a->b) -> [a] -> [b]; f :: Int -> Bool; map f [5,2]"
