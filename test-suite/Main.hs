import Test.Tasty
import Test.Tasty.HUnit

import Xi.Infer
import Xi.Parser
import Xi.Data
import Data.Text (unpack, Text)

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

-- get the toplevel type of a fully annotated expression
typeof :: Expr -> Type
typeof (Declaration _ _ e) = typeof e
typeof (Signature _ _ e) = typeof e
typeof (AnnE _ t) = t
typeof (AppE _ t) = typeof t
typeof t = error ("No annotation found for: " <> show t)

exprTestGood :: Text -> Type -> TestTree
exprTestGood e t = testCase (unpack e) (do
    x <- runStack (typecheck (readExpr e)) 0
    case x of
      (Right e') -> assertEqual "" t (typeof e')
      (Left err) -> error (show err)
  )

exprTestFull :: Text -> Text -> TestTree
exprTestFull code expCode = testCase (unpack code) (do
    x <- runStack (typecheck (readExpr code)) 0
    case x of
      (Right e) -> assertEqual "" e (readExpr expCode) 
      (Left err) -> error (show err)
  )

exprTestBad :: Text -> TestTree
exprTestBad e = testCase ("Fails?: " <> unpack e) (do
    x <- runStack (typecheck (readExpr e)) 0
    case x of
      (Right _) -> assertFailure . unpack $ "Expected '" <> e <> "' to fail"
      (Left _) -> return ()
  )

int = VarT (TV "Int")
bool = VarT (TV "Bool")
num = VarT (TV "Num")
str = VarT (TV "Str")
fun [] = error "Cannot infer type of empty list"
fun [t] = t
fun (t:ts) = FunT t (fun ts)
forall [] t = t
forall (s:ss) t = Forall (TV s) (forall ss t)  
var s = VarT (TV s)
arr s ts = ArrT (TV s) ts 
lst t = arr "List" [t]

unitTests = testGroup "Unit tests"
  [
      exprTestGood "42" int
    , exprTestGood "True" bool
    , exprTestGood "4.2" num
    , exprTestGood "\"this is a string literal\"" str
    , exprTestGood "42 :: Int" int
    , exprTestGood "True :: Bool" bool
    , exprTestGood "4.2 :: Num" num
    , exprTestGood "\"this is a string literal\" :: Str" str
    , exprTestGood "f :: Int -> Int; f (42 :: Int)" int
    , exprTestGood "(\\x -> True)" (forall ["a"] (fun [var "a", bool]))
    , exprTestGood "(\\x -> True) 42" bool
    , exprTestGood "(\\x -> (\\y -> True) x) 42" bool
    , exprTestGood "(\\x -> (\\y -> x) True) 42" int
    , exprTestGood "(\\x y->x) 1 True" int
    , exprTestGood "(\\x y -> x) :: forall a b . a -> b -> a"
                   (forall ["a","b"] (fun [var "a", var "b", var "a"]))
    , exprTestGood "((\\x -> x) :: forall a . a -> a) True" bool
    , exprTestGood "((\\x y -> x) :: forall a b . a -> b -> a) True"
                   (forall ["a"] (fun [var "a", bool]))
    , exprTestGood "x = True; 4.2" num
    , exprTestGood "x = True; (\\y -> y) x" bool
    , exprTestGood "f = (\\x y -> x); f 42"
                   (forall ["a"] (fun [var "a", int]))
    , exprTestGood "f = (\\x y -> x); x = f 42; x"
                   (forall ["a"] (fun [var "a", int]))
    , exprTestGood "x :: Int" int
    , exprTestGood "xs :: Foo a" (arr "Foo" [var "a"])
    , exprTestGood "f :: forall a . a -> a; f 42" int
    , exprTestGood "apply :: (Int -> Bool) -> Int -> Bool; f :: Int -> Bool; apply f 42"  bool 
    , exprTestGood "apply :: forall a b . (a->b) -> a -> b; f :: Int -> Bool; apply f 42" bool
    , exprTestGood "[1,2,3]" (lst int)
    , exprTestGood "[]" (forall ["a"] (lst (var "a")))
    , exprTestGood "f :: [Int] -> Bool; f [1]" bool
    , exprTestGood "f :: forall a . [a] -> Bool; f [1]" bool
    , exprTestGood "map :: forall a b . (a->b) -> [a] -> [b]; f :: Int -> Bool; map f [5,2]" (lst bool)
    -- failing tests
    , exprTestBad "[1,2,True]"
    , exprTestBad "\\x -> y" -- unbound variable
    -- internal
    , exprTestFull "f :: forall a . a -> Bool; f 42"
                   "f :: forall a . a -> Bool; (((f :: Int -> Bool) (42 :: Int)) :: Bool)"
  ]
