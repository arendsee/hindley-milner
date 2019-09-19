module UnitTests
( 
  unitTests
) where

import Xi.Infer
import Xi.Parser
import Xi.Data

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T

main :: [Module] -> [Expr]
main [] = error "Missing main"
main (m:ms)
  | moduleName m == (MV "Main") = moduleBody m
  | otherwise = main ms

-- get the toplevel type of a fully annotated expression
typeof :: [Expr] -> Type
typeof es = typeof' . head . reverse $ es where
  typeof' (Signature _ e) = case toType e of
    (Just t) -> t
    Nothing -> error $ "No general type found for: " <> show e
  typeof' (AnnE _ t) = t
  typeof' (AppE _ t) = typeof' t
  typeof' t = error ("No annotation found for: " <> show t)

exprTestGood :: String -> T.Text -> Type -> TestTree
exprTestGood msg code t
  = testCase msg
  $ case runStack (typecheck (readProgram code)) of
      (Right es', _) -> assertEqual "" t (typeof (main es'))
      (Left err, _) -> error $  "The following error was raised: " <> show err
                             <> "\nin:\n" <> show code

exprTestFull :: String -> T.Text -> T.Text -> TestTree
exprTestFull msg code expCode
  = testCase msg
  $ case runStack (typecheck (readProgram code)) of
      (Right e, _) -> assertEqual "" (main e) (main $ readProgram expCode) 
      (Left err, _) -> error (show err)

exprTestBad :: String -> T.Text -> TestTree
exprTestBad msg e
  = testCase msg
  $ case runStack (typecheck (readProgram e)) of
      (Right _, _) -> assertFailure . T.unpack $ "Expected '" <> e <> "' to fail"
      (Left _, _) -> return ()

expectError :: String -> T.Text -> TypeError -> TestTree
expectError msg expr err = testCase msg
  $ case runStack (typecheck (readProgram expr)) of
      (Right _, _) -> assertFailure . T.unpack $ "Expected failure"
      (Left err, _) -> return ()
      (Left err', _) -> assertFailure
        $ "Expected error (" <> show err <> ") got error (" <> show err' <> ")"

testPasses :: String -> T.Text -> TestTree
testPasses msg e
  = testCase msg
  $ case runStack (typecheck (readProgram e)) of
      (Right _, _) -> return ()
      (Left e, _) -> assertFailure $ "Expected this test to pass, but it failed with the message: " <> show e

int = VarT (TV "Num")
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
  v = (TV . T.pack) ("Tuple" ++ show (length ts))
record rs = RecT (map (\(x,t)->(TV x, t)) rs)

unitTests = testGroup "Unit tests"
  [
    -- primitives
      exprTestGood "primitive integer" "42" num
    , exprTestGood "primitive big integer" "123456789123456789123456789" num
    , exprTestGood "primitive decimal" "4.2" num
    , exprTestGood "primitive negative number" "-4.2" num
    , exprTestGood "primitive positive number (with sign)" "+4.2" num
    , exprTestGood "primitive scientific large exponent" "4.2e3000" num
    , exprTestGood "primitive scientific irregular" "123456789123456789123456789e-3000" num
    , exprTestGood "primitive big real" "123456789123456789123456789.123456789123456789123456789" num
    , exprTestGood "primitive boolean" "True" bool
    , exprTestGood "primitive string" "\"this is a string literal\"" str
    , exprTestGood "primitive integer annotation" "42 :: Num" num
    , exprTestGood "primitive boolean annotation" "True :: Bool" bool
    , exprTestGood "primitive double annotation" "4.2 :: Num" num
    , exprTestGood "primitive string annotation" "\"this is a string literal\" :: Str" str
    , exprTestGood "primitive declaration" "x = True; 4.2" num
    -- declarations
    , exprTestGood "identity function declaration and application" "f x = x; f 42" num
    , exprTestGood "snd function declaration and application" "snd x y = y; snd True 42" num
    , exprTestGood "explicit annotation within an application" "f :: Num -> Num; f (42 :: Num)" num
    -- lambdas
    , exprTestGood "fully applied lambda (1)" "(\\x y -> x) 1 True" num
    , exprTestGood "fully applied lambda (2)" "(\\x -> True) 42" bool
    , exprTestGood "fully applied lambda (3)" "(\\x -> (\\y -> True) x) 42" bool
    , exprTestGood "fully applied lambda (4)" "(\\x -> (\\y -> x) True) 42" num
    , exprTestGood "unapplied lambda, polymorphic (1)" "(\\x -> True)" (forall ["a"] (fun [var "a", bool]))
    , exprTestGood "unapplied lambda, polymorphic (2)"
                   "(\\x y -> x) :: forall a b . a -> b -> a"
                   (forall ["a","b"] (fun [var "a", var "b", var "a"]))
    , exprTestGood "annotated, fully applied lambda" "((\\x -> x) :: forall a . a -> a) True" bool
    , exprTestGood "annotated, partially applied lambda"
                   "((\\x y -> x) :: forall a b . a -> b -> a) True"
                   (forall ["a"] (fun [var "a", bool]))
    , exprTestGood "recursive functions are A-OK"
                   "\\f -> f 5"
                   (forall ["a"] (fun [fun [num, var "a"], var "a"]))
    -- applications
    , exprTestGood "primitive variable in application" "x = True; (\\y -> y) x" bool
    , exprTestGood "function variable in application"
                   "f = (\\x y -> x); f 42"
                   (forall ["a"] (fun [var "a", num]))
    , exprTestGood "partially applied function variable in application"
                   "f = (\\x y -> x); x = f 42; x"
                   (forall ["a"] (fun [var "a", num]))
    , exprTestBad "applications with too many arguments fail" "f :: forall a . a; f Bool 12" 
    , exprTestBad "applications with mismatched types fail (1)" "abs :: Num -> Num; abs True"
    , exprTestBad "applications with mismatched types fail (2)" "f = 14; g = \\x h -> h x; (g True) f"
    , expectError "arguments to a function are monotypes" 
                  "f :: forall a . a -> a; g = \\h -> (h 42, h True); g f"
                  (SubtypeError num bool)
    , exprTestGood  "polymorphism under lambdas (203f8c) (1)"
                    "f :: forall a . a -> a; g = \\h -> (h 42, h 1234); g f"
                    (tuple [num, num])
    , exprTestGood  "polymorphism under lambdas (203f8c) (2)"
                    "f :: forall a . a -> a; g = \\h -> [h 42, h 1234]; g f"
                    (lst num)
    , expectError "applications of non-funcions should fail (1)" "f = 5; g = \\x -> f x; g 12" NonFunctionDerive
    , expectError "applications of non-funcions should fail (2)" "f = 5; g = \\h -> h 5; g f" NonFunctionDerive
    -- binding
    , exprTestGood "annotated variables without definition are legal" "x :: Num" num
    , exprTestGood "unannotated variables with definition are legal" "x = 42; x" num
    , exprTestBad "unannotated variables without definitions are illegal ('\\x -> y')" "\\x -> y"
    -- parameterized types
    , exprTestGood "parameterized type (n=1)" "xs :: Foo a" (arr "Foo" [var "a"])
    , exprTestGood "parameterized type (n=2)" "xs :: Foo a b" (arr "Foo" [var "a", var "b"])
    , exprTestGood "nested parameterized type" "xs :: Foo (Bar a) [b]"
                   (arr "Foo" [arr "Bar" [var "a"], arr "List" [var "b"]])
    -- type signatures and higher-order functions
    , exprTestGood "type signature: identity function" "f :: forall a . a -> a; f 42" num
    , exprTestGood "type signature: apply function with primitives"
                   "apply :: (Num -> Bool) -> Num -> Bool; f :: Num -> Bool; apply f 42"  bool
    , exprTestGood "type signature: generic apply function"
                   "apply :: forall a b . (a->b) -> a -> b; f :: Num -> Bool; apply f 42" bool
    , exprTestGood "type signature: map" "map :: forall a b . (a->b) -> [a] -> [b]; f :: Num -> Bool; map f [5,2]" (lst bool)
    -- shadowing
    , exprTestGood "name shadowing in lambda expressions" "f = \\x -> (14,x); g = \\x f -> f x; g True f" (tuple [num, bool])
    , exprTestGood "shadowed qualified type variables (7ffd52a)"     "f :: forall a . a -> a; g :: forall a . a -> Num; g f" num
    , exprTestGood "non-shadowed qualified type variables (7ffd52a)" "f :: forall a . a -> a; g :: forall b . b -> Num; g f" num
    -- lists
    , exprTestGood "list of primitives" "[1,2,3]" (lst num)
    , exprTestGood "list containing an applied variable" "f :: forall a . a -> a; [53, f 34]" (lst num)
    , exprTestGood "empty list" "[]" (forall ["a"] (lst (var "a")))
    , exprTestGood "list in function signature and application" "f :: [Num] -> Bool; f [1]" bool
    , exprTestGood "list in generic function signature and application" "f :: forall a . [a] -> Bool; f [1]" bool
    , exprTestBad "failure on heterogenous list" "[1,2,True]"
    -- tuples
    , exprTestGood "tuple of primitives" "(4.2, True)" (arr "Tuple2" [num, bool])
    , exprTestGood "tuple containing an applied variable" "f :: forall a . a -> a; (f 53, True)" (tuple [num, bool])
    -- records
    , exprTestGood "primitive record statement" "{x=42, y=\"yolo\"}" (record [("x", num), ("y", str)])
    , exprTestGood "primitive record signature" "Foo :: {x :: Num, y :: Str}" (record [("x", num), ("y", str)])
    , exprTestGood "primitive record declaration" "foo = {x = 42, y = \"yolo\"}; foo" (record [("x", num), ("y", str)])
    , exprTestGood "nested records" "Foo :: {x :: Num, y :: {bob :: Num, tod :: Str}}"
                   (record [("x", num), ("y", record [("bob", num), ("tod", str)])])
    , exprTestGood "records with variables" "a=42; b={x=a, y=\"yolo\"}; f=\\b->b; f b" (record [("x", num), ("y", str)])
    -- extra space
    , exprTestGood "leading space" " 42" num
    , exprTestGood "trailing space" "42 " num
    -- adding signatures to declarations
    , exprTestGood "declaration with a signature (1)" "f :: forall a . a -> a; f x = x; f 42" num
    , exprTestGood "declaration with a signature (2)" "f :: Num -> Bool; f x = True; f 42" bool
    , exprTestGood "declaration with a signature (3)" "f :: Num -> Bool; f x = True; f" (fun [num, bool])
    , expectError  "primitive type mismatch should raise error" "f :: Num -> Bool; f x = 9999"
                   (SubtypeError num bool)

    -- tests modules
    , exprTestGood "basic Main module" "module Main {[1,2,3]}" (lst num)
    , (flip $ exprTestGood "import/export") (lst num) $ T.unlines
        [ "module Foo {export x; x = 42};"
        , "module Bar {export f; f :: forall a . a -> [a]};"
        , "module Main {import Foo (x); import Bar (f); f x}"
        ]
    , (flip $ expectError "fail on import of Main") CannotImportMain $ T.unlines
        [ "module Main {export x; x = 42};"
        , "module Foo {import Main (x)}"
        ]
    , (flip $ expectError "fail on import of non-existing variable") (BadImport (MV "Foo") (EV "x")) $ T.unlines
        [ "module Foo {export y; y = 42};"
        , "module Main {import Foo (x); x}"
        ]
    , (flip $ expectError "fail on cyclic dependency") CyclicDependency $ T.unlines
        [ "module Foo {import Bar (y); export x; x = 42};"
        , "module Bar {import Foo (x); export y; y = 88}"
        ]
    , (flip $ expectError "fail on redundant module declaration") (MultipleModuleDeclarations (MV "Foo")) $ T.unlines
        [ "module Foo {x = 42};"
        , "module Foo {x = 88}"
        ]
    , (flip $ expectError "fail on self import") (SelfImport (MV "Foo")) $ T.unlines
        [ "module Foo {import Foo (x); x = 42}"
        ]
    , (flip $ expectError "fail on import of non-exported variable") (BadImport (MV "Foo") (EV "x")) $ T.unlines
        [ "module Foo {x = 42};"
        , "module Main {import Foo (x); x}"
        ]
    -- test realization integration
    , (flip $ exprTestGood "a realization can be defined following general type signature") num $ T.unlines
        [ "f :: Num -> Num;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "realizations can map one general type to multiple specific ones ") num $ T.unlines
        [ "f :: Num -> Num;"
        , "f r :: integer -> numeric;"
        , "f 44"
        ]
    , (flip $ exprTestGood "realizations can map multiple general type to one specific one") (var "Nat") $ T.unlines
        [ "f :: Num -> Nat;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "multiple realizations for different languages can be defined") num $ T.unlines
        [ "f :: Num -> Num;"
        , "f r :: integer -> integer;"
        , "f c :: int -> int;"
        , "f 44"
        ]
    , (flip $ exprTestGood "realizations with parameterized variables") num $ T.unlines
        [ "f :: [Num] -> Num;"
        , "f r :: integer -> integer;"
        , "f c :: int -> int;"
        , "f [44]"
        ]
    , (flip $ exprTestGood "realizations can use quoted variables") num $ T.unlines
        [ "sum :: Num -> Num;"
        , "sum c :: \"double*\" -> double;"
        , "sum cpp :: \"std::vector<double>\" -> double;"
        , "sum 12"
        ]
    , (flip $ exprTestGood "the order of general signatures and realizations does not matter (1)") num $ T.unlines
        [ "f r :: integer -> integer;"
        , "f :: Num -> Num;"
        , "f c :: int -> int;"
        , "f 44"
        ]
    , (flip $ exprTestGood "the order of general signatures and realizations does not matter (2)") num $ T.unlines
        [ "f r :: integer -> integer;"
        , "f c :: int -> int;"
        , "f :: Num -> Num;"
        , "f 44"
        ]
    , (flip $ exprTestGood "multiple realizations for a single language can be defined") num $ T.unlines
        [ "f :: Num -> Num;"
        , "f r :: integer -> integer;"
        , "f r :: int -> int;"
        , "f 44"
        ]
    , (flip $ expectError "a general signature must be given") (UnboundVariable (EV "f")) $ T.unlines
        [ "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "no general type signature is required if it can be inferred") num $ T.unlines
        [ "f r :: integer -> integer;"
        , "f = \\x -> 42;"
        , "f 44"
        ] 
    , (flip $ expectError "arguments number in realizations must equal the general case (1)") BadRealization $ T.unlines
        [ "f :: Num -> String -> Num;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ expectError "arguments number in realizations must equal the general case (2)") (BadRealization) $ T.unlines
        [ "f   :: Num -> Num;"
        , "f r :: integer -> integer -> string;"
        , "f 44"
        ]
    -- internal
    , exprTestFull "every sub-expression should be annotated in output"
                   "f :: forall a . a -> Bool; f 42"
                   "f :: forall a . a -> Bool; (((f :: Num -> Bool) (42 :: Num)) :: Bool)"
  ]
