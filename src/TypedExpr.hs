module TypedExpr
( 
    TypedExpr(..)
  , Arg(..)
  , typeOf
  , retype
) where

import Type

type Name = String

data Arg = Arg Name Name deriving(Eq, Ord)

instance Show Arg where
  show (Arg n _) = n

data TypedExpr
  = EVar Name Type          -- Variable
  | EApp TypedExpr TypedExpr Type     -- Application
  | EArr Arg TypedExpr Type     -- Abstraction
  | ELet Name TypedExpr TypedExpr Type -- Let
  deriving(Show, Eq, Ord)

typeOf :: TypedExpr -> Type
typeOf (EVar _ t) = t
typeOf (EApp _ _ t) = t
typeOf (EArr _ _ t) = t
typeOf (ELet _ _ _ t) = t

retype :: Type -> TypedExpr -> TypedExpr
retype t (EVar n _) = EVar n t
retype t (EApp a b _) = EApp a b t
retype t (EArr a b _) = EArr a b t
retype t (ELet a b c _) = ELet a b c t
