module Lib (
    MonoType(..)
  , PolyType(..)
  , newvar

) where

import qualified Data.Set as S
import qualified Control.Monad.State as MS

-- infixl 1 |>>
-- (|>>) :: Functor f => f a -> (a -> b) -> f b
-- (|>>) = flip fmap

type Name = String

-- data NudeExpr
--   = NudeEVar Name           -- Variable
--   | NudeAppl Expr Expr      -- Application
--   | NudeAbst Name Expr      -- Abstraction
--   | NudeLet Name Expr Expr  -- Let
--
-- data Expr
--   = EVar Name MonoType          -- Variable
--   | Appl Expr Expr MonoType     -- Application
--   | Abst Name Expr MonoType     -- Abstraction
--   | Let Name Expr Expr MonoType -- Let

data MonoType
  = TVar Name
  | TAppl MonoType MonoType
  deriving(Show, Eq, Ord)

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

newvar :: J Name
newvar = do
  s <- MS.get
  let v = "x" ++ show (index s)
  MS.put (s {index = index s + 1})
  return v


-- inst :: PolyType -> J MonoType
-- inst = inst' [] where
--   inst' :: [(Name, Name)] -> PolyType -> J MonoType
--   inst' xs (ForAll n t) = newvar >>= (\v -> inst' ((n, v):xs) t)
--   inst' xs (PVar t) = return t
--
--   instMono :: [(Name, Name)] -> MonoType -> MonoType
--   instMono xs (TVar n) = maybe (TVar n) TVar (lookup n xs)
--   instMono xs (TAppl t1 t2) = TAppl (instMono xs t1) (instMono xs t2)

--
-- data Typing = Typing Context Expr MonoType
--
-- class Typed a where
--   free :: a -> S.Set MonoType
--
-- instance Typed Typing where
--   free (Typing context _ polytype) = free polytype \\ free context
--
-- instance Typed Context where
--   free (Context xs) = S.fromList $ mapM (free . snd) xs
--
-- instance Typed PolyType where
--   free (PVar t) = free t
--   free (ForAll n t) = S.delete n (free t)
--
-- instance Typed MonoType where
--   free (TVar n) = S.singleton n
--   free (TAppl xs) = S.fromList $ mapM free xs
--
-- data Predicate
--   = IsSubset PolyType PolyType
--   | IsBound Name Context
--   | IsDefined Name Name Context
--
-- data Premise
--   = PPredicate Predicate
--   | PTyping Typing
--
-- type Judgement = Typing
-- type Conclusion = Judgement

-- addContext :: (Name,Name) -> J ()
-- addContext c = do
--   s <- MS.get
--   MS.put (s {context = c : context s})
--
-- tag :: MonoType -> NudeExpr -> Expr
-- tag (NudeEVar n) t = EVar t n
-- tag (NudeAppl n e) t = Appl t n e
-- tag (NudeAbst n e) t = Abst t n e
-- tag (NudeLet n e1 e2) t = Let t n e1 e2
--
-- -- data Expr
-- --   = EVar Name MonoType          -- Variable
-- --   | Appl Expr Expr MonoType     -- Application
-- --   | Abst Name Expr MonoType     -- Abstraction
-- --   | Let Name Expr Expr MonoType -- Let
-- --
-- -- data MonoType
-- --   = TVar Name
-- --   | TAppl MonoType MonoType
-- --   deriving(Show, Eq, Ord)
-- --
-- -- data PolyType
-- --   = PVar MonoType
-- --   | ForAll Name PolyType
-- --   deriving(Show, Eq, Ord)
--
-- inferTypes :: NudeExpr -> J Expr
-- inferTypes (NudeEVar n) = newvar |>> EVar n
-- inferTypes (NudeAppl e1 e2) = do
--   t1' <- inferTypes e1
--   t2' <- inferTypes e1
--   t <- newvar
--   let u = unify t
--   return u
--
-- unify :: MonoType -> MonoType -> Expr -> Expr
-- unify (TVar n1) (TVar n2) = replace (TVar n1) (TVar n2)
-- unify (TAppl n1 m1) (TAppl n2 m2) = undefined
--   -- | len m1 == len m2 && n1 == n2 =
--
-- replace :: MonoType -> MonoType -> Expr -> Expr
-- replace a b = mapMonoType replace' where
--   replace' (EVar n t)
--     | a == t = EVar n b
--     | otherwise = EVar n a
--   replace' (TAppl e1 e2) = TAppl (replace a b e1) (replace a b e2)
--
-- replace a b (EVar n t)
--   | a == t = EVar n b
--   | otherwise = EVar n a
-- replace a b (TAppl e1 e2) = TAppl (replace a b e1) (replace a b e2)
--
-- mapMonoType :: (MonoType -> MonoType) -> Expr -> Expr
-- mapMonoType f (EVar n t) = EVar n (f t)
-- mapMonoType f (Appl e1 e2 t) = Appl (mapMonoType f e1) (mapMonoType f e2) (f t)
-- mapMonoType f (Abst n e t) = Abst n (mapMonoType  f e) (f t)
--
--
-- len :: MonoType -> Int
-- len (TVar _) = 1
-- len (TAppl _ m) = 1 + len m
