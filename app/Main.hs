module Main where

import DkTest

-- run :: Expr -> Stack Gamma
-- run expr = MS.runStateT (MW.runWriterT (ME.runExceptT( infer [] expr ))) 0


main :: IO ()
main = runDkTest
