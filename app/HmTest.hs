module HmTest
  ( 
    runHmTest
  ) where

import HindleyMilner.Infer as HM
import HindleyMilner.Pretty

import Data.Text.Prettyprint.Doc (pretty, line, Doc)
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

-- x
-- x:t0
e0 = Var (EV "x") "t0"

-- foo x
-- (foo:(t1->t2) x:t1):t2
e1 = App
  (Var (EV "foo") "t0")
  (Var (EV "x") "t1")
  "t2"

-- foo x y
-- ((foo:(t1 -> (t3 -> t4)) x:t1):(t3 -> t4) y:t3):t4
e2 = App
  (App (Var (EV "foo") "t0") (Var (EV "x") "t1") "t2")
  (Var (EV "y") "t3")
  "t4"

-- \ x . y x x
e3 = Lam (EV "x") "t0"
    (App
      (App
        (Var (EV "y") "t1")
        (Var (EV "x") "t2")
        "t3"
      )
      (Var (EV "x") "t4")
      "t5"
    ) "t6"
-- (\ x:t0 . y:(t0->t0->t1) x:t0 x:t0):(t0->t1)

-- let x = f y in h x
e4 = Let
  (EV "x")
  "t0"
  (App
    (Var (EV "f") "t1")
    (Var (EV "y") "t2")
    "t3")
  (App
    (Var (EV "h") "t4")
    (Var (EV "x") "t5")
    "t6")
  "t7"

-- let id = \x -> x in h (id True) (id 42)
e5 = Let
  (EV "id")
  "t0"
  (Lam
    (EV "x")
    "t1"
    (Var (EV "x") "t2")
    "t3"
  )
  (App
    (App
        (Var (EV "h") "t4")
        (App
          (Var (EV "id") "t5")
          (Lit (PBool True) "t6")
          "t7"
        )
        "t8"
    )
    (App
      (Var (EV "id") "t8")
      (Lit (PInt 42) "t10")
      "t11"
    )
    "t12"
  )
  "t13"


writeType :: Expr String -> IO ()
writeType e = do
  putStrLn "================================="
  putDoc $ pretty e <> line
  putStrLn "---"
  putDoc $ prettyTerm (inferTypes e []) <> line

runHmTest :: IO ()
runHmTest = do
  writeType e0
  writeType e1
  writeType e2
  writeType e3
  writeType e4
  writeType e5
