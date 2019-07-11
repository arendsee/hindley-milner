module Main where

import Lib
import qualified Control.Monad.State as MS

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
  print $ MS.evalState (inferTypes e0) initJState
  print $ MS.evalState (inferTypes e1) initJState
  print $ MS.evalState (inferTypes e2) initJState
  print $ MS.evalState (inferTypes e3) initJState
  print $ MS.evalState (inferTypes e4) initJState
