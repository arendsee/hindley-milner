module Bidirectional.Simple.Infer (
    infer
  , emptyContext
) where

import Bidirectional.Simple.Data
import Bidirectional.Simple.Parser
import qualified Data.Map as Map

class Extendable a where
  extend :: a -> Type -> Gamma -> Gamma

instance Extendable EVar where
  extend e t (Gamma g) = Gamma (Map.insert e t g) 

instance Extendable Expr where
  extend (Var v) t g = extend v t g
  extend _ _ g = g

emptyContext = Gamma (Map.empty)

lookupEnv :: EVar -> Gamma -> Infer
lookupEnv e@(EV x) (Gamma g) = case Map.lookup e g of
  Just t -> return t
  Nothing -> throw $ UnboundVariable x

-- | infer calls check when it reaches a type annotation
infer :: Gamma -> Expr -> Infer
infer g (Var v) = lookupEnv v g
infer g outer@(App (Lam v e1) e2) = do
  t <- infer g e2
  infer (extend v t g) e1
infer _ e@(App _ _) = throw $ CallingNonfunction e
infer g e@(Lam _ _) = throw $ NeedExplicitTypeSignature e
infer g e@(If e1 e2 e3) = do
  check g e1 TBool
  t2 <- infer g e2
  check g e3 t2
  return t2
infer g (Ann e t) = check (extend e t g) e t
infer _ (Lit _) = return TBool

-- | check calls infer when it reaches something that can be inferred
check :: Gamma -> Expr -> Type -> Infer
check g e@(Var _) t = do
  t' <- infer g e
  if t' == t then return t else (throw $ TypeMismatch e t t')
check g (App (Lam v e1) e2) t = check g e2 t >> infer (extend v t g) e1
check _ e@(App _ _) _ = throw $ CallingNonfunction e
check g (Lam v e) t = infer (extend v t g) e  
check g (If e1 e2 e3) t = do
  check g e1 TBool
  check g e2 t
  check g e3 t
  return t
check g (Ann e t) _ = check g e t
check _ (Lit _) TBool = return TBool 
check _ l@(Lit _) _ = throw (BadLiterature l)
