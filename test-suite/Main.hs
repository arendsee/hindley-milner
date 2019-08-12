import Test.Tasty
-- import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC
import Test.Tasty.HUnit

import Data.List
import Data.Ord
import Bidirectional.Dunfield.Infer
import Bidirectional.Dunfield.Parser
import Bidirectional.Dunfield.Data (runStack, Type)
import Data.Text.Prettyprint.Doc

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

-- tests :: TestTree
-- tests = testGroup "Tests" [properties, unitTests]
--
-- properties :: TestTree
-- properties = testGroup "Properties" [scProps, qcProps]
--
-- scProps = testGroup "(checked by SmallCheck)"
--   [ SC.testProperty "sort == sort . reverse" $
--       \list -> sort (list :: [Int]) == sort (reverse list)
--   , SC.testProperty "Fermat's little theorem" $
--       \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , SC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 SC.==> x^n + y^n /= (z^n :: Integer)
--   ]
--
-- qcProps = testGroup "(checked by QuickCheck)"
--   [ QC.testProperty "sort == sort . reverse" $
--       \list -> sort (list :: [Int]) == sort (reverse list)
--   , QC.testProperty "Fermat's little theorem" $
--       \x -> ((x :: Integer)^7 - x) `mod` 7 == 0
--   -- the following property does not hold
--   , QC.testProperty "Fermat's last theorem" $
--       \x y z n ->
--         (n :: Integer) >= 3 QC.==> x^n + y^n /= (z^n :: Integer)
--   ]

exprTestGood :: String -> String -> TestTree
exprTestGood e t = testCase e (do
    x <- runStack (typecheck (readExpr e)) 0
    case x of
      (Right t') -> assertEqual "" t (show $ pretty t')
      (Left err) -> error (show err)
  )

exprTestBad :: String -> TestTree
exprTestBad e = testCase ("Fails?: " <> e) (do
    x <- runStack (typecheck (readExpr e)) 0
    case x of
      (Right t') -> assertFailure $ "Expected '" <> e <> "' to fail"
      (Left _) -> return ()
  )


unitTests = testGroup "Unit tests"
  [
      exprTestGood "42" "Int"
    , exprTestGood "True" "Bool"
    , exprTestGood "4.2" "Num"
    , exprTestGood "\"this is a string literal\"" "Str"
    , exprTestGood "(\\x -> True)" "forall a . a -> Bool"
    , exprTestGood "(\\x -> True) 42" "Bool"
    , exprTestGood "(\\x -> (\\y -> True) x) 42" "Bool"
    , exprTestGood "(\\x -> (\\y -> x) True) 42" "Int"
    , exprTestGood "(\\x y->x) 1 True" "Int"
    , exprTestGood "(\\x y -> x) :: forall a b . a -> b -> a" "forall a b . a -> b -> a"
    , exprTestGood "((\\x -> x) :: forall a . a -> a) True" "Bool"
    , exprTestGood "((\\x y -> x) :: forall a b . a -> b -> a) True" "forall a . a -> Bool"
    , exprTestGood "x = True; 4.2" "Num"
    , exprTestGood "x = True; (\\y -> y) x" "Bool"
    , exprTestGood "f = (\\x y -> x); f 42" "forall a . a -> Int"
    , exprTestGood "f = (\\x y -> x); x = f 42; x" "forall a . a -> Int"
    , exprTestGood "x :: Int" "Int"
    , exprTestGood "xs :: Foo a" "Foo a"
    , exprTestGood "f :: forall a . a -> a; f 42" "Int"
    , exprTestGood "apply :: forall a b . (a->b) -> a -> b; f :: Int -> Bool; apply f 42" "Bool"
    , exprTestGood "[1,2,3]" "List Int"
    , exprTestGood "[]" "forall a . List a"
    , exprTestGood "f :: [Int] -> Bool; f [1]" "Bool"
    , exprTestGood "f :: forall a . [a] -> Bool; f [1]" "Bool"
    , exprTestGood "map :: forall a b . (a->b) -> [a] -> [b]; f :: Int -> Bool; map f [5,2]" "List Bool"
    -- failing tests
    , exprTestBad "[1,2,True]"
  ]


