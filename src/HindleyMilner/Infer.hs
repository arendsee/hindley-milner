module HindleyMilner.Infer ( 
    Expr(..)
  , Type(..)
  , EVar(..)
  , TVar(..)
  , TLiteral(..)
  , Literal(..)
  , inferTypes
  , nullGamma
) where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Bifunctor
import qualified Control.Monad.State as MS
import qualified Control.Monad.Except as ME
import Debug.Trace (trace)

newtype TVar = TV String deriving(Show, Ord, Eq)
newtype EVar = EV String deriving(Show, Ord, Eq)

data Expr a
  = Var EVar a
  | App (Expr a) (Expr a) a
  | Lam EVar a (Expr a) a
  | Let EVar a (Expr a) (Expr a) a
  | Lit Literal a
  deriving(Show, Ord, Eq)

data Literal
  = PInt Int
  | PBool Bool
  deriving(Show, Ord, Eq)

data Type
  = TVar TVar
  | TArr Type Type
  | TLit TLiteral
  deriving(Show, Ord, Eq)

data TLiteral
  = TInt
  | TBool
  deriving(Show, Ord, Eq)

newtype Subst = Subst (Map.Map TVar Type) deriving (Show, Ord, Eq)

newtype Gamma = Gamma (Map.Map EVar Type) deriving (Show, Ord, Eq)

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Gamma where
  apply (Subst s) (Gamma g) = Gamma (Map.map f g) where 
    f :: Type -> Type
    f t@(TVar v) = maybe t id (Map.lookup v s)
    f x = x

instance Substitutable (Expr Type) where
  apply s = fmap (apply s) where

instance Substitutable Type where
  apply s@(Subst m) t@(TVar v) = case Map.lookup v m of
    Nothing -> t
    (Just t'@(TVar _)) -> t'
    (Just t') -> apply s t'
  apply s (TArr t1 t2) = TArr (apply s t1) (apply s t2)
  apply _ x@(TLit _) = x

instance Functor Expr where
  fmap f (Var (EV s) t)          = Var (EV s) (f t)
  fmap f (App e1 e2 t)             = App (fmap f e1) (fmap f e2) (f t)
  fmap f (Lam (EV s) t' e1 t)    = Lam (EV s) (f t') (fmap f e1) (f t)
  fmap f (Let (EV s) t' e1 e2 t) = Let (EV s) (f t') (fmap f e1) (fmap f e2) (f t)
  fmap f (Lit l t)                 = Lit l (f t)

pull :: Expr a -> a
pull (Var _ t)       = t
pull (App _ _ t)     = t
pull (Lam _ _ _ t)   = t
pull (Let _ _ _ _ t) = t
pull (Lit _ t)       = t

compose :: Subst -> Subst -> Subst
compose (Subst s1) (Subst s2) = Subst (Map.union s1 s2)

extend :: EVar -> Type -> Gamma -> Gamma
extend n t (Gamma g) = Gamma (Map.insert n t g)

restrict :: EVar -> Gamma -> Gamma
restrict n (Gamma g) = Gamma (Map.delete n g)

nullSubst :: Subst
nullSubst = Subst Map.empty

nullGamma :: Gamma
nullGamma = Gamma Map.empty

pair :: TVar -> Type -> Subst 
pair v t = Subst $ Map.singleton v t

lookupEnv :: Gamma -> EVar -> TVar -> (Subst, Type)
lookupEnv (Gamma g) n x = case Map.lookup n g of
    (Just t) -> (pair x t, t)
    Nothing -> (pair x (TVar x), (TVar x))

inferTypes :: Expr String -> [(String, Type)] -> Expr Type
inferTypes e env = apply s (fmap TVar e')
  where
    e' :: Expr TVar
    e' = fmap TV e

    g :: Gamma
    g = Gamma . Map.fromList $ map (\(s,t) -> (EV s, t)) env

    s :: Subst
    s = fst $ infer g e'

unify :: Type -> Type -> Subst
unify (TVar v) t = pair v t 
unify t (TVar v) = pair v t 
unify (TLit t1) (TLit t2) | t1 == t2 = nullSubst
unify t1 t2 = error $ "Cannot unify '" <> show t1 <> "' and '" <> show t2 <> "'"

infer :: Gamma -> Expr TVar -> (Subst, Type)
infer g e = case e of

  --  x:s in Env
  --  -----------------------------------------------------
  --  Env |- x:s
  Var n t' -> lookupEnv g n t'

  --  Env |- e1 : t1
  --  Env |- e2 : t2
  --  -----------------------------------------------------
  --  Env |- e1 e2 : t2
  App e1 e2 t' -> (sf, tf)
    where
      tv = TVar t'
      (s1, t1) = infer g e1
      (s2, t2) = infer (apply s1 g) e2
      s3 = unify (apply s2 t1) (TArr t2 tv)
      sf = s3 `compose` s2 `compose` s1
      tf = apply s3 tv

  --  Env |- x : t'
  --  Env, x : t' |- e : t2
  --  -----------------------------------------------------
  --  Env |- \x -> e : t' -> t2
  Lam n t1' e t2' -> (sf, tf)
    where
      tb = TVar t1'
      g' = extend n tb g
      (s1, t1) = infer g' e
      tf = TArr (apply s1 tb) t1
      sf = s1 `compose` (pair t2' tf)

  --  Env |- e1:t1
  --  Env, n:t1 |- e2:t'
  --  -----------------------------------------------------
  --  Env |- let n=e1 in e2 : t'
  Let n tvar e1 e2 tlet -> (s1 `compose` s2 `compose` (pair tlet t2), t2)
    where
      (s1, t1) = infer g e1
      g' = extend n t1 g  -- bind the type of e1 to the variable
      s' = apply s1 g'
      (s2, t2) = infer s' e2

  Lit (PInt _) t' -> (pair t' (TLit TInt), TLit TInt)
  Lit (PBool _) t' -> (pair t' (TLit TBool), TLit TBool)


{----------------------------------------------------------

let const = \x y -> x in const 1 True

-------------------------------------------------------------------
|                                | what I want to infer           |
-------------------------------------------------------------------
|  1   Let                       | : Int                          |
|  2    |--- Lam                 | : Forall a b . a -> (b -> a)   |
|  3    |    |--- Var x *        | : t1                           |
|  4    |    `--- Lam            | : Forall a . a -> t1           |
|  5    |         |--- Var y *   | : t2                           |
|  6    |         `--- Var x     | : t1                           |
|  7    |--- Var const *         | : Forall a b . a -> (b -> a)   |
|  8    `-- App                  | : Bool -> Int                  |
|  9        |--- App             | : Int -> Bool -> Int           |
| 10        |    |--- const      | : Int -> Bool -> Int           |
| 11        |    `--- Int 1      | : Int                          |
| 12        `--- Bool True       | : Bool                         |
-------------------------------------------------------------------

--------------------------------------------------------}
