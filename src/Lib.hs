module Lib (
    inferTypes
  , RawExpr(..)
) where

import qualified Data.Set as S
import qualified Control.Monad.State as MS

infixl 1 |>>
(|>>) :: Functor f => f a -> (a -> b) -> f b
(|>>) = flip fmap

type Name = String

data RawExpr
  = V Name                 -- Variable
  | A RawExpr RawExpr      -- Application
  | S Name RawExpr         -- Abstraction
  | L Name RawExpr RawExpr -- Let
  deriving(Show, Eq, Ord)

data Expr
  = EVar Name MonoType          -- Variable
  | Appl Expr Expr MonoType     -- Application
  | Abst Name Expr MonoType     -- Abstraction
  | Let Name Expr Expr MonoType -- Let
  deriving(Eq, Ord)

instance Show Expr where
  show (EVar n t) = n ++ ":" ++ show t
  show (Appl e1 e2 t) = "(" ++ show e1 ++ " " ++ show e2 ++ "):" ++ show t
  show (Abst n e t) = "(\\" ++ n ++ " . " ++ show e ++ "):" ++ show t 
  show (Let n e1 e2 t) = "(let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ":)" ++ show t

data MonoType
  = TVar Name
  | TAppl MonoType MonoType
  deriving(Eq, Ord)

instance Show MonoType where
  show (TVar n) = n
  show (TAppl t1 t2) = show t1 ++ " " ++ show t2  

data PolyType
  = PVar MonoType
  | ForAll Name PolyType
  deriving(Show, Eq, Ord)

-- a symbol table defining all terms that have a type within this scope
type Context = [(Name, MonoType)]

data HMState = HMState {
    context :: Context
  , index :: Int
}
type J = MS.State HMState;

initJState :: HMState
initJState = HMState {
      context = []
    , index = 0
  }

newvar :: J MonoType
newvar = do
  s <- MS.get
  let v = TVar $ "x" ++ show (index s)
  MS.put (s {index = index s + 1})
  return v

-- Recursively assign each expression to a unique type variable
inst :: RawExpr -> J Expr
inst (V n) = newvar |>> EVar n
inst (A e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ Appl e1' e2' t'
inst (S n e) = do
  t' <- newvar
  e' <- inst e
  return $ Abst n e' t'
inst (L n e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ Let n e1' e2' t'

inferTypes :: RawExpr -> Expr
inferTypes e = MS.evalState (inst e) initJState
