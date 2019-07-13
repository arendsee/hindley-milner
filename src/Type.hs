module Type( 
    Type(..)
  , function
  , fromFunction
) where

import qualified Data.Map as Map
import qualified Data.Set as Set

type Name = String

data Type
  = TVar Name 
  | TArr Type Type
  deriving(Show, Eq, Ord)

function :: Type -> Type -> Type
function t1 t2 = t1 `TArr` (TVar "->") `TArr` t2

fromFunction :: Type -> Maybe (Type, Type)
fromFunction (t1 `TArr` (TVar "->") `TArr` t2) = Just (t1, t2)
fromFunction _ = Nothing
