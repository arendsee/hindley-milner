module Bidirectional.Simple.Infer (
    infer
  , emptyContext
) where

import Bidirectional.Simple.Data
import Bidirectional.Simple.Parser
import qualified Data.Map as Map

class Extendable a where
  extend :: a -> Type -> Gamma -> Gamma

instance Extendable VarE where
  extend e t (Gamma g) = Gamma (Map.insert e t g) 

instance Extendable Expr where
  extend (Var v) t g = extend v t g
  extend _ _ g = g

emptyContext = Gamma (Map.empty)

lookupEnv :: VarE -> Gamma -> Infer
lookupEnv e@(VE x) (Gamma g) = case Map.lookup e g of
  Just t -> return t
  Nothing -> throw $ UnboundVariable x


-- | infer calls check when it reaches a type annotation
infer :: Gamma -> Expr -> Infer
infer g (Var v) = lookupEnv v g
infer g (App (Lam v e1) e2) = do
  t <- infer g e2
  infer (extend v t g) e1
infer g e@(App e1 e2) = case infer g e1 of
    (Right (LamT t1 t2)) -> check g e2 t1 >> return t2
    _ -> throw $ NeedExplicitTypeSignature e
infer g (If e1 e2 e3) = do
  check g e1 LogT
  t <- (infer g e2 >>= check g e3) <>
       (infer g e3 >>= check g e2)
  return t
infer g (Ann e t) = check (extend e t g) e t
infer _ (Log _) = return LogT
infer _ (Num _) = return NumT
infer g e@(Lst (x:_)) = do
  t <- infer g x
  check g e (LstT t)
infer _ (Lst []) = throw EmptyList 
infer _ e@(App _ _) = throw $ CallingNonfunction e
infer _ e@(Lam _ _) = throw $ NeedExplicitTypeSignature e

-- | check calls infer when it reaches something that can be inferred
check :: Gamma -> Expr -> Type -> Infer
check g e@(Var _) t = do
  t' <- infer g e
  if t' == t then return t else (throw $ TypeMismatch e t t')
check g (App (Lam v e1) e2) t = check g e2 t >> infer (extend v t g) e1
check g (Lam v e) t = infer (extend v t g) e  
check g (If e1 e2 e3) t = do
  check g e1 LogT
  check g e2 t
  check g e3 t
  return t
check g (Ann e t) _ = check g e t
check _ (Lst [])     l@(LstT _) = return l
check g (Lst (x:xs)) l@(LstT t) = do
  check g x t
  check g (Lst xs) l
check _ (Num _) NumT = return NumT
check _ (Log _) LogT = return LogT
-- failing cases
check _ e@(Log _  ) t = throw $ TypeMismatch e LogT t
check _ e@(App _ _) _ = throw $ CallingNonfunction e
check _ e@(Num _  ) t = throw $ TypeMismatch e NumT t
check _ e@(Lst _  ) t = throw $ ListTypeMismatch e t
