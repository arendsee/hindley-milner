module Main where

import Lib
import Pretty

-- x
e0 = V "foo"

-- foo x
e1 = A (V "foo") (V "x")

-- foo x y
e2 = A (A (V "foo") (V "x")) (V "y")

-- \ x . y x x
e3 = S "x" (A (A (V "y") (V "x")) (V "x"))

-- let x = f y in h x
e4 = L "x" (A (V "f") (V "y")) (A (V "h") (V "x"))

main :: IO ()
main = do
  putStr "x ==> "
  putStrLn . pretty $ inferTypes e0
  putStr "foo x ==> "
  putStrLn . pretty $ inferTypes e1
  putStr "foo x y ==> "
  putStrLn . pretty $ inferTypes e2
  putStr "\\x -> y x x ==> "
  putStrLn . pretty $ inferTypes e3
  putStr "let x = f y in h x ==> "
  putStrLn . pretty $ inferTypes e4
