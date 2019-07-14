module Main where

import Lib
import Pretty

import Data.Text.Prettyprint.Doc (pretty, line, Doc)
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

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

writeType :: Expr -> Doc a -> IO ()
writeType e d = do
  putDocW 80 d
  putDoc $ prettyTerm (inferTypes e) <> line

main :: IO ()
main = do
  writeType e0 "x ==> "
  writeType e1 "foo x ==> "
  writeType e2 "foo x y ==> "
  writeType e3 "\\x -> y x x ==> "
  writeType e4 "let x = f y in h x ==> "
