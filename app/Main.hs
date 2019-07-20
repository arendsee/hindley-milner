module Main where

import Infer
import Pretty

import Data.Text.Prettyprint.Doc (pretty, line, Doc)
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

-- x
e0 = Var (EV "x") "t0"

-- foo x
e1 = App (Var (EV "foo") "t0") (Var (EV "x") "t1") "t2"

-- -- foo x y
-- e2 = A (A (V "foo") (V "x")) (V "y")
--
-- -- \ x . y x x
-- e3 = S "x" (A (A (V "y") (V "x")) (V "x"))
--
-- -- let x = f y in h x
-- e4 = L "x" (A (V "f") (V "y")) (A (V "h") (V "x"))

writeType :: Expr String -> IO ()
writeType e = do
  putStrLn "================================="
  putDoc $ pretty e <> line
  putStrLn "---"
  putDoc $ prettyTerm (inferTypes e []) <> line

main :: IO ()
main = do
  writeType e0
  writeType e1
  -- writeType e2
  -- writeType e3
  -- writeType e4
