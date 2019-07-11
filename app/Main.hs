module Main where

import Lib

-- x
e0 = V "foo"

-- foo x
e1 = A (V "foo") (V "x")

-- foo x y
e2 = A (A (V "foo") (V "x")) (V "y")

-- \ x . y x
e3 = S "x" (A (V "y") (V "x"))

-- let x = f y in h x
e4 = L "x" (A (V "f") (V "y")) (A (V "h") (V "x"))

main :: IO ()
main = do
  print $ inferTypes e0
  print $ inferTypes e1
  print $ inferTypes e2
  print $ inferTypes e3
  print $ inferTypes e4
