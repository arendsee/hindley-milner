module BD.Data
(
    Expr(..)
  , EVar(..)
  , Type(..)
  , Gamma(..)
) where

import qualified Data.Map as Map

newtype EVar = EV String deriving(Show, Ord, Eq)

newtype Gamma = Gamma (Map.Map EVar Type) 

data Expr
  = Var EVar 
  | App Expr Expr
  | Lam EVar Expr
  | Lit Bool
  | If Expr Expr Expr
  | Ann Expr Type -- ^ A type annotation
  deriving(Show, Ord, Eq)

data Type
  = TEmpty
  | TBool
  | TLam Type Type -- ^ t1 -> t2
  deriving(Show, Ord, Eq)
