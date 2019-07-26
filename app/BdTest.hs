module BdTest
  ( 
    runBdTest
  ) where

import Bidirectional.Simple.Infer
import Bidirectional.Simple.Parser

import Data.Text.Prettyprint.Doc

showExpr :: String -> IO ()
showExpr x = do
  putStrLn $ "----------------------------------------------------------"
  putStrLn x
  let e = readExpr x 
  -- print e
  case infer emptyContext e of
    Right t -> print $ "_ :: " <> pretty t
    Left err -> print $ "ERROR" <+> pretty err
  putStr "\n"

runBdTest :: IO ()
runBdTest = do
  showExpr "map :: [a]"
  showExpr "[1,2,3]"
  showExpr "if true then [1,2,3] else [4,4,4]"
  showExpr "if true then [1,2,3] else []"
  showExpr "if true then [] else [1,2,3]"
  showExpr "if true then false else true"
  showExpr "(f :: [Num] -> [Bool]) [1,2,3]"

--   showExpr "f :: Bool"
--   showExpr "f :: Bool -> Bool -> Bool"
--   showExpr "f :: (Bool -> Bool) -> Bool -> Bool"
--   showExpr "true"
--   showExpr "f :: List Int Int"
--
--   -- negative tests that should fail
--   showExpr "f (true :: Bool)" -- FAIL: undefined toplevel lambda
--   showExpr "(f :: Int -> Int) (true :: Int)" -- FAIL: bad annotation
--
-- -- Some tests
--   -- -- Here, the semicolons would be parsed into nested let expressions
--   -- showExpr "map :: (a->b) -> [a] -> [b]); f :: Int -> Int; map f [1,2,3]"
--
-- -- tests of things that do not work yet but should be implemented
--   -- inference of bound variables under lambdas (sometimes it is possible)
--   showExpr "\\ x -> if x then 1 else 0"
--
--   -- type variables - need some sort of substitution as well as generalization
--   -- to polytypes
--   showExpr "(id :: a -> a) 42"
--   showExpr "((map :: (a->b) -> [a] -> [b]) (f :: Int -> Bool)) [1,2,3]"
