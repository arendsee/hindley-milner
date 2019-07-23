module Bidirectional.Simple.Data
(
    Expr(..)
  , EVar(..)
  , Type(..)
  , Gamma(..)
  , Infer(..)
  , TypeError(..)
  , throw
) where

import qualified Data.Map as Map

newtype EVar = EV String deriving(Show, Ord, Eq)

newtype Gamma = Gamma (Map.Map EVar Type) 

type Infer = Either TypeError Type

throw :: TypeError -> Infer 
throw err = Left err

data TypeError
  = BadThingHappened Expr
  | CallingNonfunction Expr
  | IfelseBlockTypeMismatch Expr
  | NeedExplicitTypeSignature Expr
  | UnboundVariable String
  | TypeMismatch Expr Type Type
  | BadLiterature Expr
  deriving(Show, Ord, Eq)

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
