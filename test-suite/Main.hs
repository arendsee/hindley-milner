import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

import Xi.Infer
import Xi.Parser
import Xi.Data
import Data.Text (unpack, pack, Text)
import qualified Data.Set as Set

main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, propertyTests]

-- get the toplevel type of a fully annotated expression
typeof :: Expr -> Type
typeof (Declaration _ _ e) = typeof e
typeof (Signature _ _ e) = typeof e
typeof (AnnE _ t) = t
typeof (AppE _ t) = typeof t
typeof t = error ("No annotation found for: " <> show t)

exprTestGood :: Text -> Type -> TestTree
exprTestGood e t
  = testCase (unpack e)
  $ case runStack (typecheck (readExpr e)) 0 of
      (Right e', _) -> assertEqual "" t (typeof e')
      (Left err, _) -> error (show err)

exprTestFull :: Text -> Text -> TestTree
exprTestFull code expCode
  = testCase (unpack code)
  $ case runStack (typecheck (readExpr code)) 0 of
      (Right e, _) -> assertEqual "" e (readExpr expCode) 
      (Left err, _) -> error (show err)

exprTestBad :: Text -> TestTree
exprTestBad e
  = testCase ("Fails?: " <> unpack e)
  $ case runStack (typecheck (readExpr e)) 0 of
      (Right _, _) -> assertFailure . unpack $ "Expected '" <> e <> "' to fail"
      (Left _, _) -> return ()

expectError :: Text -> TypeError -> TestTree
expectError expr err = testCase ("Fails?: " <> unpack expr)
  $ case runStack (typecheck (readExpr expr)) 0 of
      (Right _, _) -> assertFailure . unpack $ "Expected failure"
      (Left err, _) -> return ()
      (Left err', _) -> assertFailure
        $ "Expected error (" <> show err <> ") got error (" <> show err' <> ")"

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
tuple ts = ArrT v ts where
  v = (TV . pack) ("Tuple" ++ show (length ts))

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
    , exprTestGood "(4.2, True)" (arr "Tuple2" [num, bool])
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
    , exprTestGood "f :: forall a . a -> a; [53, f 34]" (lst int)
    , exprTestGood "f :: forall a . a -> a; (f 53, True)" (tuple [int, bool])
    , exprTestGood "[]" (forall ["a"] (lst (var "a")))
    , exprTestGood "f :: [Int] -> Bool; f [1]" bool
    , exprTestGood "f :: forall a . [a] -> Bool; f [1]" bool
    -- * higher order functions
    , exprTestGood "map :: forall a b . (a->b) -> [a] -> [b]; f :: Int -> Bool; map f [5,2]" (lst bool)
    , exprTestGood "f = \\x -> (14,x); g = \\x f -> f x; g True f" (tuple [int, bool])
    -- * fails to terminate when qualified type variables are not distinguished
    -- See commit 7ffd52a
    , exprTestGood "f :: forall a . a -> a; g :: forall a . a -> Int; g f" int
    , exprTestGood "f :: forall a . a -> a; g :: forall b . b -> Int; g f" int
    -- failing tests ----------------------------------------------------------
    -- * heterogenous list
    , exprTestBad "[1,2,True]"
    -- * unbound variable
    , exprTestBad "\\x -> y"
    -- * too many arguments
    , exprTestBad "f :: forall a . a; f Bool 12"
    -- * arguments have the wrong type
    , exprTestBad "abs :: Int -> Int; abs True"
    -- * arguments to a function are monotypes
    , expectError   "f :: forall a . a -> a; g = \\h -> (h 42, h True); g f"
                    (SubtypeError int bool)
    , exprTestGood  "f :: forall a . a -> a; g = \\h -> (h 42, h 1234); g f"
                    (tuple [int, int])
    -- * find misuses
    , exprTestBad "f = 14; g = \\x h -> h x; (g True) f"
    --             ^               ^    ^ this should fail
    -- ------------+---------------'----'

    -- These should all fail, since f is not a function
    , expectError "f = 5; g = \\x -> f x; g 12" NonFunctionDerive
    , expectError "f = 5; g = \\h -> h 5; g f" NonFunctionDerive
    , exprTestGood "\\f -> f 5" 
                   (forall ["a"] (fun [fun [int, var "a"], var "a"]))
                   -- forall a . (Int -> a) -> a

    -- internal ---------------------------------------------------------------
    , exprTestFull "f :: forall a . a -> Bool; f 42"
                   "f :: forall a . a -> Bool; (((f :: Int -> Bool) (42 :: Int)) :: Bool)"
  ]

-- remove all type annotations and type signatures
unannotate :: Expr -> Expr
unannotate (AnnE e t) = unannotate e
unannotate (ListE xs) = ListE (map unannotate xs)
unannotate (TupleE xs) = TupleE (map unannotate xs)
unannotate (LamE v e) = LamE v (unannotate e)
unannotate (AppE e1 e2) = AppE (unannotate e1) (unannotate e2)
unannotate (Declaration v e1 e2) = Declaration v (unannotate e1) (unannotate e2)
unannotate (Signature v t e) = unannotate e
unannotate e = e

annotationOf :: Expr -> Maybe Type
annotationOf (AnnE e t) = Just t
annotationOf _ = Nothing

typeSize :: Type -> Int
typeSize (UniT) = 1
typeSize (VarT _) = 1
typeSize (ExistT _) = 1
typeSize (Forall _ t) = 1 + typeSize t
typeSize (FunT t1 t2) = 1 + typeSize t1 + typeSize t2
typeSize (ArrT _ xs) = 1 + sum (map typeSize xs) 

subtypeOf :: Type -> Type -> Gamma -> Bool
subtypeOf t1 t2 g =
  case runStack (subtype t1 t2 g) 0 of
    (Right _, _) -> True
    (Left _, _) -> False

infer1 :: Expr -> Bool
infer1 e = case runStack (infer [] e) 0 of
  (Right (g, t, e'), _) -> infer1' t e' 
  (Left e, _) -> False
  where
    infer1' t (Declaration _ _ e2) = infer1' t e2
    infer1' t (Signature _ _ e2) = infer1' t e2
    infer1' t e2 = case (annotationOf e2) of
      (Just t') -> t' == t
      Nothing -> False

infer2 :: Expr -> Bool
infer2 e = case runStack (infer [] e) 0 of
  (Right (g, t, e'), _) -> unannotate e == unannotate e'
  (Left _, _) -> False

renameTest :: Expr -> Bool
renameTest e = case runStack (renameExpr e) 0 of
  (Right e', _) -> unrenameExpr e' == e
  (Left _, _) -> False

propertyTests = testGroup "Property tests"
  [
   -- generalization
     QC.testProperty "size(Gen(t)) >= size(t)" $
       \t -> typeSize (generalize t) >= typeSize t
   -- quantifier term renaming
   , QC.testProperty "e == unrename(rename e)" renameTest
   -- substitution
   , QC.testProperty "size([v/<v>]t) == size(t)" $
       \(v,t) -> typeSize (substitute v t) == typeSize t
   -- subtype tests
   , QC.testProperty "t <: t" $
       \t -> subtypeOf t t []
   -- generalizeE tests
   , QC.testProperty "unannotate(e) == unannotate(generalizeE(e))" $
       \e -> unannotate e == unannotate (generalizeE e)
   -- apply
   , QC.testProperty "apply [] t == t" $
      \t -> apply [] t == t
   -- applyE
   , QC.testProperty "applyE [] e == e" $
      \e -> applyE [] e == e    
   -- free
   , QC.testProperty "length(free t) <= size t" $
      \t -> Set.size (free t) <= typeSize t
   -- infer1 
   , QC.testProperty "i4.2 == annotationOf(i4.3)" infer1
   -- infer2 
   , QC.testProperty "unannotate e == unannotate (infer e)" infer2
  ]
