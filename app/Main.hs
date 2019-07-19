module Main where

import Infer

import Data.Text.Prettyprint.Doc (pretty, line, Doc)
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

-- x
e0 = Var (EV "x") "a0"

-- foo x
e1 = App (Var (EV "foo") "a0") (Var (EV "x") "a1") "a2"

-- -- foo x y
-- e2 = A (A (V "foo") (V "x")) (V "y")
--
-- -- \ x . y x x
-- e3 = S "x" (A (A (V "y") (V "x")) (V "x"))
--
-- -- let x = f y in h x
-- e4 = L "x" (A (V "f") (V "y")) (A (V "h") (V "x"))

-- writeType :: Expr -> IO ()
-- writeType e = do
--   putStrLn "================================="
--   putDoc $ pretty e <> line
--   putStrLn "---"
--   putDoc $ prettyTerm (infer e) <> line

main :: IO ()
main = do
  print $ inferTypes e0 [("x", TVar (TV "t1"))]
  print $ inferTypes e1 []
  -- writeType e0
  -- writeType e1
  -- writeType e2
  -- writeType e3
  -- writeType e4
