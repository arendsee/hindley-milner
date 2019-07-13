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

data Arg = Arg Name Name deriving(Eq, Ord)

instance Show Arg where
  show (Arg n _) = n

data TypedExpr
  = EVar Name MonoType          -- Variable
  | Appl TypedExpr TypedExpr MonoType     -- Application
  | Abst Arg TypedExpr MonoType     -- Abstraction
  | Let Name TypedExpr TypedExpr MonoType -- Let
  deriving(Eq, Ord)

instance Show TypedExpr where
  show (EVar n t) = n ++ ":" ++ show t
  show (Appl e1 e2 t) = "(" ++ show e1 ++ " " ++ show e2 ++ "):" ++ show t
  show (Abst (Arg n _) e t) = "(\\" ++ n ++ " . " ++ show e ++ "):" ++ show t 
  show (Let n e1 e2 t) = "(let " ++ n ++ " = " ++ show e1 ++ " in " ++ show e2 ++ ":):" ++ show t

data MonoType
  = TVar Name
  | TAppl MonoType MonoType
  deriving(Eq, Ord)

instance Show MonoType where
  show (TVar n) = n
  show (TAppl (TAppl (TVar "->") t1) t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (TAppl t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"

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

typeOf :: TypedExpr -> MonoType
typeOf (EVar _ t) = t
typeOf (Appl _ _ t) = t
typeOf (Abst _ _ t) = t
typeOf (Let _ _ _ t) = t

retype :: MonoType -> TypedExpr -> TypedExpr
retype t (EVar n _) = EVar n t
retype t (Appl a b _) = Appl a b t
retype t (Abst a b _) = Abst a b t
retype t (Let a b c _) = Let a b c t

newname :: J Name 
newname = do
  s <- MS.get
  let v = "x" ++ show (index s)
  MS.put (s {index = index s + 1})
  return v

newvar :: J MonoType
newvar = fmap TVar newname

-- Recursively assign each expression to a unique type variable
inst :: RawExpr -> J TypedExpr
inst (V n) = newvar |>> EVar n
inst (A e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ Appl e1' e2' t'
inst (S n e) = do
  t' <- newvar
  r' <- newname
  e' <- inst e
  return $ Abst (Arg n r') e' t'
inst (L n e1 e2) = do
  t' <- newvar
  e1' <- inst e1
  e2' <- inst e2
  return $ Let n e1' e2' t'

inferTypes :: RawExpr -> TypedExpr
inferTypes e
  = apply
  . bind []
  $ MS.evalState (inst e) initJState

bind :: [(Name, MonoType)] -> TypedExpr -> TypedExpr
bind xs (EVar n t) = maybe (EVar n t) (EVar n) (lookup n xs)
bind xs (Appl e1 e2 t) = Appl (bind xs e1) (bind xs e2) t
bind xs (Abst (Arg n t1) e t2)
  = Abst (Arg n t1) (bind xs' e) t2 where
    xs' = (n,TVar t1):(filter (\(n',_) -> n' /= n) xs)
bind xs (Let n e1 e2 t2) = Let n e1 e2' t2'
  where
    t1' = typeOf e1
    xs' = (n,t1'):(filter (\(n', _) -> n' /= n) xs)
    e2' = bind xs' e2
    t2' = typeOf e2'

apply :: TypedExpr -> TypedExpr
apply (Appl e1{-t0-} e2{-t1-} t{-t2-}) = Appl e1''{-(t4->t5)-} e2'{-t4-} t'{-t5-}
  where
    e2' = apply e2 -- |- t4
    e1' = apply e1 -- |- t5
    t' = typeOf e1'
    t6 = function (typeOf e2') t' -- |- (t4 -> t5)
    e1'' = retype t6 e1'
apply e = e

function :: MonoType -> MonoType -> MonoType
function t1 t2 = TAppl (TAppl (TVar "->") t1) t2
