module Lib (
    inferTypes
  , Expr(..)
) where

import Expr
import State
import TypedExpr
import Type
import qualified Control.Monad.State as MS
import qualified Data.Set as Set
import qualified Data.Map as Map

type Name = String

newvar :: Infer Type
newvar = fmap TVar newname


inferTypes :: Expr -> TypedExpr
inferTypes e
  = apply
  . bind Map.empty
  $ MS.evalState (inst e) initState


-- Give expression a unique type name
inst :: Expr -> Infer TypedExpr
inst (V n) = do
  t' <- newvar
  return $ EVar n t'
inst (A e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ EApp e1' e2' t'
inst (S n e) = do
  t' <- newvar
  r' <- newname
  e' <- inst e
  return $ EArr (Arg n r') e' t'
inst (L n e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ ELet n e1' e2' t'


addToEnv :: Name -> Type -> Map.Map Name Type -> Map.Map Name Type
addToEnv = Map.insert


removeFromEnv :: Name -> Map.Map Name Type -> Map.Map Name Type
removeFromEnv = Map.delete


bind :: Map.Map Name Type -> TypedExpr -> TypedExpr
bind xs t0@(EVar n _) = maybe t0 (EVar n) (Map.lookup n xs)
bind xs (EApp e1 e2 t) = EApp (bind xs e1) (bind xs e2) t
bind xs (EArr (Arg n t1) e t2)
  = EArr (Arg n t1) (bind xs' e) t2 where
    xs' = addToEnv n (TVar t1) xs
bind xs (ELet n e1 e2 t2) = ELet n e1 e2' t2'
  where
    t1' = typeOf e1
    xs' = addToEnv n t1' xs
    e2' = bind xs' e2
    t2' = typeOf e2'


apply :: TypedExpr -> TypedExpr
apply (EApp e1{-t0-} e2{-t1-} t{-t2-}) = EApp e1''{-(t4->t5)-} e2'{-t4-} t'{-t5-}
  where
    e2' = apply e2 -- |- t4
    e1' = apply e1 -- |- t5
    t' = typeOf e1'
    t6 = function (typeOf e2') (typeOf e1') -- |- (t4 -> t5)
    e1'' = retype t6 e1'
apply (EArr a e t) = EArr a e' t' where
  e' = apply e
  t' = case fromFunction t of 
    Just (t1, t2) -> function (typeOf e') t2
    Nothing -> t 
apply (EVar n t) = EVar n t
apply (ELet n e1 e2 t) = ELet n e1' e2' t'
  where
    e1' = apply e1
    e2' = apply e2
    t' = typeOf e2'
