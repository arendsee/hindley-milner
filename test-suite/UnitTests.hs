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
  v = (TV . T.pack) ("Tuple" ++ show (length ts))

unitTests = testGroup "Unit tests"
  [
    -- primitives
      exprTestGood "primitive integer" "42" int
    , exprTestGood "primitive boolean" "True" bool
    , exprTestGood "primitive double" "4.2" num
    , exprTestGood "primitive string" "\"this is a string literal\"" str
    , exprTestGood "primitive integer annotation" "42 :: Int" int
    , exprTestGood "primitive boolean annotation" "True :: Bool" bool
    , exprTestGood "primitive double annotation" "4.2 :: Num" num
    , exprTestGood "primitive string annotation" "\"this is a string literal\" :: Str" str
    , exprTestGood "primitive declaration" "x = True; 4.2" num
    -- declarations
    , exprTestGood "identity function declaration and application" "f x = x; f 42" int
    , exprTestGood "snd function declaration and application" "snd x y = y; snd True 42" int
    , exprTestGood "explicit annotation within an application" "f :: Int -> Int; f (42 :: Int)" int
    -- lambdas
    , exprTestGood "fully applied lambda (1)" "(\\x y -> x) 1 True" int
    , exprTestGood "fully applied lambda (2)" "(\\x -> True) 42" bool
    , exprTestGood "fully applied lambda (3)" "(\\x -> (\\y -> True) x) 42" bool
    , exprTestGood "fully applied lambda (4)" "(\\x -> (\\y -> x) True) 42" int
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
                   (forall ["a"] (fun [fun [int, var "a"], var "a"]))
    -- applications
    , exprTestGood "primitive variable in application" "x = True; (\\y -> y) x" bool
    , exprTestGood "function variable in application"
                   "f = (\\x y -> x); f 42"
                   (forall ["a"] (fun [var "a", int]))
    , exprTestGood "partially applied function variable in application"
                   "f = (\\x y -> x); x = f 42; x"
                   (forall ["a"] (fun [var "a", int]))
    , exprTestBad "applications with too many arguments fail" "f :: forall a . a; f Bool 12" 
    , exprTestBad "applications with mismatched types fail (1)" "abs :: Int -> Int; abs True"
    , exprTestBad "applications with mismatched types fail (2)" "f = 14; g = \\x h -> h x; (g True) f"
    , expectError "arguments to a function are monotypes" 
                  "f :: forall a . a -> a; g = \\h -> (h 42, h True); g f"
                  (SubtypeError int bool)
    , exprTestGood  "polymorphism under lambdas (203f8c) (1)"
                    "f :: forall a . a -> a; g = \\h -> (h 42, h 1234); g f"
                    (tuple [int, int])
    , exprTestGood  "polymorphism under lambdas (203f8c) (2)"
                    "f :: forall a . a -> a; g = \\h -> [h 42, h 1234]; g f"
                    (lst int)
    , expectError "applications of non-funcions should fail (1)" "f = 5; g = \\x -> f x; g 12" NonFunctionDerive
    , expectError "applications of non-funcions should fail (2)" "f = 5; g = \\h -> h 5; g f" NonFunctionDerive
    -- binding
    , exprTestGood "annotated variables without definition are legal" "x :: Int" int
    , exprTestGood "unannotated variables with definition are legal" "x = 42; x" int
    , exprTestBad "unannotated variables without definitions are illegal ('\\x -> y')" "\\x -> y"
    -- parameterized types
    , exprTestGood "parameterized type (n=1)" "xs :: Foo a" (arr "Foo" [var "a"])
    , exprTestGood "parameterized type (n=2)" "xs :: Foo a b" (arr "Foo" [var "a", var "b"])
    , exprTestGood "nested parameterized type" "xs :: Foo (Bar a) [b]"
                   (arr "Foo" [arr "Bar" [var "a"], arr "List" [var "b"]])
    -- type signatures and higher-order functions
    , exprTestGood "type signature: identity function" "f :: forall a . a -> a; f 42" int
    , exprTestGood "type signature: apply function with primitives"
                   "apply :: (Int -> Bool) -> Int -> Bool; f :: Int -> Bool; apply f 42"  bool
    , exprTestGood "type signature: generic apply function"
                   "apply :: forall a b . (a->b) -> a -> b; f :: Int -> Bool; apply f 42" bool
    , exprTestGood "type signature: map" "map :: forall a b . (a->b) -> [a] -> [b]; f :: Int -> Bool; map f [5,2]" (lst bool)
    -- shadowing
    , exprTestGood "name shadowing in lambda expressions" "f = \\x -> (14,x); g = \\x f -> f x; g True f" (tuple [int, bool])
    , exprTestGood "shadowed qualified type variables (7ffd52a)"     "f :: forall a . a -> a; g :: forall a . a -> Int; g f" int
    , exprTestGood "non-shadowed qualified type variables (7ffd52a)" "f :: forall a . a -> a; g :: forall b . b -> Int; g f" int
    -- lists
    , exprTestGood "list of primitives" "[1,2,3]" (lst int)
    , exprTestGood "list containing an applied variable" "f :: forall a . a -> a; [53, f 34]" (lst int)
    , exprTestGood "empty list" "[]" (forall ["a"] (lst (var "a")))
    , exprTestGood "list in function signature and application" "f :: [Int] -> Bool; f [1]" bool
    , exprTestGood "list in generic function signature and application" "f :: forall a . [a] -> Bool; f [1]" bool
    , exprTestBad "failure on heterogenous list" "[1,2,True]"
    -- tuples
    , exprTestGood "tuple of primitives" "(4.2, True)" (arr "Tuple2" [num, bool])
    , exprTestGood "tuple containing an applied variable" "f :: forall a . a -> a; (f 53, True)" (tuple [int, bool])
    -- extra space
    , exprTestGood "leading space" " 42" int
    , exprTestGood "trailing space" "42 " int
    -- adding signatures to declarations
    , exprTestGood "declaration with a signature (1)" "f :: forall a . a -> a; f x = x; f 42" int
    , exprTestGood "declaration with a signature (2)" "f :: Int -> Bool; f x = True; f 42" bool
    , exprTestGood "declaration with a signature (3)" "f :: Int -> Bool; f x = True; f" (fun [int, bool])
    , expectError  "primitive type mismatch should raise error" "f :: Int -> Bool; f x = 9999"
                   (SubtypeError int bool)

    -- tests modules
    , exprTestGood "basic Main module" "module Main {[1,2,3]}" (lst int)
    , (flip $ exprTestGood "import/export") (lst int) $ T.unlines
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
    , (flip $ exprTestGood "a realization can be defined following general type signature") int $ T.unlines
        [ "f :: Int -> Int;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "realizations can map one general type to multiple specific ones ") int $ T.unlines
        [ "f :: Int -> Int;"
        , "f r :: integer -> numeric;"
        , "f 44"
        ]
    , (flip $ exprTestGood "realizations can map multiple general type to one specific one") (var "Nat") $ T.unlines
        [ "f :: Int -> Nat;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "multiple realizations for different languages can be defined") int $ T.unlines
        [ "f :: Int -> Int;"
        , "f r :: integer -> integer;"
        , "f c :: int -> int;"
        , "f 44"
        ]
    , (flip $ exprTestGood "the order of general signatures and realizations does not matter (1)") int $ T.unlines
        [ "f r :: integer -> integer;"
        , "f :: Int -> Int;"
        , "f c :: int -> int;"
        , "f 44"
        ]
    , (flip $ exprTestGood "the order of general signatures and realizations does not matter (2)") int $ T.unlines
        [ "f r :: integer -> integer;"
        , "f c :: int -> int;"
        , "f :: Int -> Int;"
        , "f 44"
        ]
    , (flip $ exprTestGood "multiple realizations for a single language can be defined") int $ T.unlines
        [ "f :: Int -> Int;"
        , "f r :: integer -> integer;"
        , "f r :: int -> int;"
        , "f 44"
        ]
    , (flip $ expectError "a general signature must be given") (UnboundVariable (EV "f")) $ T.unlines
        [ "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ exprTestGood "no general type signature is required if it can be inferred") int $ T.unlines
        [ "f r :: integer -> integer;"
        , "f = \\x -> 42;"
        , "f 44"
        ] 
    , (flip $ expectError "arguments number in realizations must equal the general case (1)") BadRealization $ T.unlines
        [ "f :: Int -> String -> Int;"
        , "f r :: integer -> integer;"
        , "f 44"
        ]
    , (flip $ expectError "arguments number in realizations must equal the general case (2)") (BadRealization) $ T.unlines
        [ "f   :: Int -> Int;"
        , "f r :: integer -> integer -> string;"
        , "f 44"
        ]
    -- internal
    , exprTestFull "every sub-expression should be annotated in output"
                   "f :: forall a . a -> Bool; f 42"
                   "f :: forall a . a -> Bool; (((f :: Int -> Bool) (42 :: Int)) :: Bool)"
  ]
