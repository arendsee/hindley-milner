module BD.Infer
( 
    infer
  , check
  , readExpr
) where

import BD.Data
import BD.Parser

infer :: Gamma -> Expr -> Maybe Type
infer = undefined

check :: Gamma -> Type -> Type -> Maybe Type
check = undefined
