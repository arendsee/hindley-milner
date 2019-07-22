module BD.Infer (
    infer
  , emptyContext
) where

import BD.Data
import BD.Parser
import qualified Data.Map as Map

extend :: EVar -> Type -> Gamma -> Gamma
extend e t (Gamma g) = Gamma (Map.insert e t g) 

lookupEnv :: EVar -> Gamma -> Maybe Type
lookupEnv e (Gamma g) = Map.lookup e g

emptyContext = Gamma (Map.empty)

-- | infer calls check when it reaches a type annotation
infer :: Gamma -> Expr -> Maybe Type
infer g (Var v) = lookupEnv v g
infer g (App (Lam v e1) e2) = case infer g e2 of
  (Just t) -> infer (extend v t g) e1 
  Nothing -> Nothing
infer _ (App _ _) = Nothing
infer g (Lam v e) = Nothing -- Cannot type a lambda function in infer mode
infer g (If e1 e2 e3) = case (infer g e1, infer g e2, infer g e3) of
  (Just TBool, Just t1, Just t2) ->
    if t1 == t2
    then Just t1
    else Nothing
  _ -> Nothing
infer g (Ann e t) = check g e t
infer _ (Lit _) = Just TBool

-- | check calls infer when it reaches something that can be inferred
check :: Gamma -> Expr -> Type -> Maybe Type
check g e@(Var _) t = case infer g e of
  (Just t') -> if t' == t then Just t else Nothing
  Nothing -> Nothing
check g (App (Lam v e1) e2) t = case check g e2 t of
  (Just _) -> infer (extend v t g) e1 
  Nothing -> Nothing
check _ (App _ _) _ = Nothing
check g (Lam v e) t = infer (extend v t g) e  
check g (If e1 e2 e3) t = case (check g e1 TBool, check g e2 t, check g e3 t) of 
    (Just _, Just _, Just _) -> Just t
    _ -> Nothing
check g (Ann e t) _ = check g e t
check _ (Lit _) TBool = Just TBool 
check _ (Lit _) _ = Nothing
