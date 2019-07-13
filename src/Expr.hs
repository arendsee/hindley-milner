module Expr ( 
  Expr(..)
) where

import Data.Set as Set

type Name = String

data Expr
  = V Name           -- Variable
  | A Expr Expr      -- Application
  | S Name Expr      -- Abstraction
  | L Name Expr Expr -- Let
  deriving(Show, Eq, Ord)

fv :: Expr -> Set.Set Name
fv (V n) = Set.singleton n
fv (A e1 e2) = Set.union (fv e1) (fv e2)
fv (S n e) = Set.delete n (fv e)
fv (L n e1 e2) = Set.delete n (Set.union (fv e1) (fv e2))
