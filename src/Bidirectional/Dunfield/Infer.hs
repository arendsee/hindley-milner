module Bidirectional.Dunfield.Infer ( typecheck ) where

import Bidirectional.Dunfield.Data
import Control.Monad.Trans (liftIO)
import Data.Text.Prettyprint.Doc
import qualified Data.List as DL
import qualified Data.Set as Set

typecheck :: Expr -> Stack Type
typecheck e = (fmap snd $ infer [] e) >>= generalize

run :: Pretty a => Doc' -> [(Doc', Doc')] -> Stack a -> Stack a
run s args x = do
  incDepth
  v <- verbosity
  d <- depth
  run1 v d
  output <- x
  run2 v d
  decDepth
  run3 v output
  return output
  where
    run1 0 _ = return ()
    run1 1 d' = do
      liftIO . print $ pretty (take d' $ repeat '>') <+> s
      mapM writeArg args
      return ()
    run2 0 _ = return ()
    run2 1 d' = do
      liftIO . print $ pretty (take d' $ repeat '<') <+> s
    run3 0 _ = return ()
    run3 1 x = do
      liftIO . print $ "  return:" <+> pretty x

writeArg :: (Doc', Doc') -> Stack ()
writeArg (name, arg) = do
  liftIO . print $ "  " <> name <> ":" <+> arg

runSubtype :: Doc' -> Type -> Type -> Gamma -> Stack Gamma -> Stack Gamma
runSubtype s t1 t2 g x
  = run ("subtype " <> s) [("t1", pretty t1), ("t2", pretty t2), ("g", pretty g)] x

runInstantiate :: Doc' -> Type -> Type -> Gamma -> Stack Gamma -> Stack Gamma
runInstantiate s t1 t2 g x
  = run ("instantiate " <> s) [("ta", pretty t1), ("tb", pretty t2), ("g", pretty g)] x

runInfer :: Doc' -> Gamma -> Expr -> Stack (Gamma, Type) -> Stack (Gamma, Type)
runInfer s g e x
  = run ("infer " <> s) [("g", pretty g), ("e", pretty e)] x

runCheck :: Doc' -> Gamma -> Expr -> Type -> Stack (Gamma, Type) -> Stack (Gamma, Type)
runCheck s g e t x
  = run ("check " <> s) [("g", pretty g), ("e", pretty e), ("t", pretty t)] x

runDerive :: Doc' -> Gamma -> Expr -> Type -> Stack (Gamma, Type) -> Stack (Gamma, Type)
runDerive s g e t x
  = run ("derive " <> s) [("g", pretty g), ("e", pretty e), ("t", pretty t)] x

generalize :: Type -> Stack Type
generalize t = generalize' existentialMap t
  where 

    generalize' :: [(TVar, TVar)] -> Type -> Stack Type
    generalize' [] t' = return t'
    generalize' ((e,r):xs) t' = generalizeOne e r t' >>= generalize' xs

    existentialMap
      = zip
        (Set.toList (findExistentials t))
        (map (TV . return) ['a'..'z'])

    findExistentials :: Type -> Set.Set TVar
    findExistentials UniT = Set.empty
    findExistentials (VarT _) = Set.empty
    findExistentials (ExistT v) = Set.singleton v
    findExistentials (Forall v t) = Set.delete v (findExistentials t)
    findExistentials (FunT t1 t2) = Set.union (findExistentials t1) (findExistentials t2)
    findExistentials (ArrT v ts) = Set.unions (map findExistentials ts)

    generalizeOne :: TVar -> TVar -> Type -> Stack Type
    generalizeOne v r t = Forall <$> pure r <*> f v t where
      f :: TVar -> Type -> Stack Type
      f v t@(ExistT v')
        | v == v' = return $ VarT r
        | otherwise = return t
      f v (FunT t1 t2) = FunT <$> (f v t1) <*> (f v t2)
      f v t@(Forall x t')
        | v /= x = Forall <$> pure x <*> f v t'
        | otherwise = throwError OccursCheckFail
      f _ t = return t


-- | substitute all appearances of a given variable with an existential
-- [t/v]A
substitute :: TVar -> Type -> Type
substitute v t@(VarT v')
  | v == v' = ExistT v
  | otherwise = t
substitute v (FunT t1 t2) = FunT (substitute v t1) (substitute v t2)
substitute v t@(Forall x t')
  | v /= x = Forall x (substitute v t')
  | otherwise = t -- allows shadowing of the variable
substitute _ t = t


-- | Apply a context to a type (See Dunfield Figure 8).
apply :: Gamma -> Type -> Type
-- [G]l = l
apply _ UniT = UniT
-- [G]a = a
apply _ a@(VarT _) = a
-- [G](A->B) = ([G]A -> [G]B)
apply g (FunT a b) = FunT (apply g a) (apply g b)
-- [G]Forall a.a = forall a. [G]a
apply g (Forall x a) = Forall x (apply g a)
-- [G[a=t]]a = [G[a=t]]t
apply g a@(ExistT v) = case lookupT v g of
  (Just t') -> apply g t' -- reduce an existential; strictly smaller term
  Nothing -> a


-- | Ensure a given type variable is not free within a given type
occursCheck :: Type -> TVar -> Stack TVar
occursCheck UniT v = return v
occursCheck (VarT v') v 
  | v' == v = throwError OccursCheckFail
  | otherwise = return v
occursCheck (FunT t1 t2) v = do
  occursCheck t1 v
  occursCheck t2 v
occursCheck (Forall v' t) v
  | v' == v = return v -- variable is bound, we are done
  | otherwise = occursCheck t v -- else recurse
occursCheck (ExistT v') v
  | v' == v = throwError OccursCheckFail -- existentials count
  | otherwise = return v'

occursCheckExpr :: Gamma -> EVar -> Stack EVar
occursCheckExpr [] v = return v
occursCheckExpr ((AnnG (VarE v') _):gs) v
  | v' == v = throwError ToplevelRedefinition
  | otherwise = occursCheckExpr gs v

-- | type 1 is more polymorphic than type 2 (Dunfield Figure 9)
subtype :: Type -> Type -> Gamma -> Stack Gamma
--
-- ----------------------------------------- Unit
--  G |- 1 <: 1 -| G
subtype UniT UniT g = runSubtype "Unit" UniT UniT g $ do
  return g
--
-- ----------------------------------------- <:Var
--  G[a] |- a <: a -| G[a]
subtype t1@(VarT a1) t2@(VarT a2) g = runSubtype "<:Var" t1 t2 g $ do
  if (a1 == a2)
  then return g
  else throwError SubtypeError
--
-- ----------------------------------------- <:Exvar
--  G[E.a] |- Ea <: Ea -| G[E.a]
subtype a@(ExistT a1) b@(ExistT a2) g = runSubtype "<:Exvar" a b g $ do
  if (a1 == a2)
  then return g
  else instantiate a b g
--  g1 |- B1 <: A1 -| g2
--  g2 |- [g2]A2 <: [g2]B2 -| g3
-- ----------------------------------------- <:-->
--  g1 |- A1 -> A2 <: B1 -> B2 -| g3
subtype x@(FunT a1 a2) y@(FunT b1 b2) g1 = runSubtype "<:-->" x y g1 $ do
  -- function subtypes are *contravariant* with respect to the input, that is,
  -- the subtypes are reversed so we have b1<:a1 instead of a1<:b1.
  g2 <- subtype b1 a1 g1
  subtype (apply g2 a2) (apply g2 b2) g2
--  g1,>Ea,Ea |- [Ea/x]A <: B -| g2,>Ea,g3
-- ----------------------------------------- <:ForallL
--  g1 |- Forall x . A <: B -| g2
subtype t@(Forall x a) b g = runSubtype "<:ForallL" t b g $ do
  subtype (substitute x a) b (g +> MarkG x +> ExistG x) >>= cut (MarkG x)
--  g1,a |- A :> B -| g2,a,g3
-- ----------------------------------------- <:ForallR
--  g1 |- A <: Forall a. B -| g2
subtype a t@(Forall v b) g = runSubtype "<:ForallR" a t g $ do
  subtype a b (g +> VarG v) >>= cut (VarG v)
--  g1 |- A1 <: B1
-- ----------------------------------------- <:App
--  g1 |- A1 A2 <: B1 B2 -| g2
--  unparameterized types are the same as VarT, so subtype on that instead
subtype (ArrT v1 []) (ArrT v2 []) g = subtype (VarT v1) (VarT v2) g
subtype t1@(ArrT v1 vs1) t2@(ArrT v2 vs2) g = runSubtype "<:App" t1 t2 g $ do
  subtype (VarT v1) (VarT v2) g
  compareArr vs1 vs2 g
  where
    compareArr :: [Type] -> [Type] -> Gamma -> Stack Gamma
    compareArr [] [] g' = return g'
    compareArr (t1:ts1) (t2:ts2) g' = do
      g'' <- subtype t1 t2 g'
      compareArr ts1 ts2 g''
    compareArr _ _ _ = throwError UnkindJackass
--  Ea not in FV(a)
--  g1[Ea] |- Ea <=: A -| g2
-- ----------------------------------------- <:InstantiateL
--  g1[Ea] |- Ea <: A -| g2
subtype a@(ExistT v) b g = runSubtype "<:InstantiateL" a b g $ do
  occursCheck b v
  instantiate a b g 
--  Ea not in FV(a)
--  g1[Ea] |- A <=: Ea -| g2
-- ----------------------------------------- <:InstantiateR
--  g1[Ea] |- A <: Ea -| g2
subtype a b@(ExistT v) g = runSubtype "<:InstantiateR" a b g $ do
  occursCheck a v
  instantiate a b g 
subtype a b g = runSubtype "<:con" a b g $ do
  throwError SubtypeError 



-- | Dunfield Figure 10 -- type-level structural recursion
instantiate :: Type -> Type -> Gamma -> Stack Gamma

--  g1[Ea2, Ea1, Ea=Ea1->Ea2] |- A1 <=: Ea1 -| g2
--  g2 |- Ea2 <=: [g2]A2 -| g3
-- ----------------------------------------- InstLArr
--  g1[Ea] |- Ea <=: A1 -> A2 -| g3
instantiate ta@(ExistT v) tb@(FunT t1 t2) g1 = runInstantiate "instLArr" ta tb g1 $ do
  ea1 <- newvar
  ea2 <- newvar
  g2 <- case access1 ta g1 of
    Just (rs, _, ls) -> return $ rs ++ [SolvedG v (FunT ea1 ea2), index ea1, index ea2] ++ ls
    Nothing -> throwError UnknownError
  g3 <- instantiate t1 ea1 g2
  g4 <- instantiate ea2 (apply g3 t2) g3
  return g4

--  g1[Ea2,Ea1,Ea=Ea1->Ea2] |- Ea1 <=: A1 -| g2
--  g2 |- [g2]A2 <=: Ea2 -| g3
-- ----------------------------------------- InstRArr
--  g1[Ea] |- A1 -> A2 <=: Ea -| g3
instantiate ta@(FunT t1 t2) tb@(ExistT v) g1 = runInstantiate "InstRArr" ta tb g1 $ do
  ea1 <- newvar
  ea2 <- newvar
  g2 <- case access1 tb g1 of
    Just (rs, _, ls) -> return $ rs ++ [SolvedG v (FunT ea1 ea2), index ea1, index ea2] ++ ls
    Nothing -> throwError UnknownError
  g3 <- instantiate t1 ea1 g2
  g4 <- instantiate ea2 (apply g3 t2) g3
  return g4

--
-- ----------------------------------------- InstLAllR
--
instantiate ta@(ExistT _) tb@(Forall v2 t2) g1 = runInstantiate "InstLAllR" ta tb g1 $ do
  instantiate ta t2 (g1 +> VarG v2) >>= cut (VarG v2)

-- InstLReach or instRReach -- each rule eliminates an existential
-- Replace the rightmost with leftmost (G[a][b] --> L,a,M,b=a,R)
-- WARNING: be careful here, since the implementation adds to the front and the
-- formal syntax adds to the back. Don't change anything in the function unless
-- you really know what you are doing and have tests to confirm it.
instantiate ta@(ExistT v1) tb@(ExistT v2) g1 = runInstantiate "Inst[LR]Reach" ta tb g1 $ do
  case access2 ta tb g1 of
    -- InstLReach
    (Just (ls, _, ms, x, rs)) -> return $ ls <> (SolvedG v1 tb:ms) <> (x:rs)
    Nothing -> case access2 tb ta g1 of
      -- InstRReach
      (Just (ls, _, ms, x, rs)) -> return $ ls <> (SolvedG v2 ta:ms) <> (x:rs)
      Nothing -> throwError UnknownError

--  g1[Ea],>Eb,Eb |- [Eb/x]B <=: Ea -| g2,>Eb,g3
-- ----------------------------------------- InstRAllL
--  g1[Ea] |- Forall x. B <=: Ea -| g2
instantiate ta@(Forall x b) tb@(ExistT _) g1 = runInstantiate "InstRSolve" ta tb g1 $ do
  instantiate
      (substitute x b)             -- [Eb/x]B
      tb                           -- Ea
      (g1 +> MarkG x +> ExistG x)  -- g1[Ea],>Eb,Eb
  >>= cut (MarkG x)
--  g1 |- t
-- ----------------------------------------- InstRSolve
--  g1,Ea,g2 |- t <=: Ea -| g1,Ea=t,g2
instantiate ta tb@(ExistT v) g1 = runInstantiate "InstRSolve" ta tb g1 $ do
  accessWith (const (SolvedG v ta)) tb g1
--  g1 |- t
-- ----------------------------------------- instLSolve
--  g1,Ea,g2 |- Ea <=: t -| g1,Ea=t,g2
instantiate ta@(ExistT v) tb g1 = runInstantiate "instLSolve" ta tb g1 $ do
  accessWith (const (SolvedG v tb)) ta g1
-- bad
instantiate t1 t2 g = runInstantiate "error" t1 t2 g $ do
  return g

infer :: Gamma -> Expr -> Stack (Gamma, Type)
-- handle primitives
infer g e@(NumE _) = runInfer "Num=>" g e $ do
  return (g, VarT (TV "Num"))
infer g e@(IntE _) = runInfer "Int=>" g e $ do
  return (g, VarT (TV "Int"))
infer g e@(StrE _) = runInfer "Str=>" g e $ do
  return (g, VarT (TV "Str"))
infer g e@(LogE _) = runInfer "Log=>" g e $ do
  return (g, VarT (TV "Bool"))
infer g e@(Declaration v e1 e2) = runInfer "Declaration=>" g e $ do
  occursCheckExpr g v
  (g', t1) <- infer g e1
  t1' <- generalize t1
  infer (g +> AnnG (VarE v) t1') e2
infer g e@(Signature v t e2) = runInfer "Signature=>" g e $ do
  infer (g +> AnnG (VarE v) t) e2

--
-- ----------------------------------------- 1l=>
--  g |- () => 1 -| g
infer g e@UniE = runInfer "1l=>" g e $ do
  return (g, UniT) 
--  (x:A) in g
-- ----------------------------=>------------- Var
--  g |- x => A -| g
infer g e@(VarE _) = runInfer "Var" g e $ do
  case lookupE e g of
    (Just t) -> return (g, t)
    Nothing  -> throwError UnboundVariable
--  g1,Ea,Eb,x:Ea |- e <= Eb -| g2,x:Ea,g3
-- ----------------------------------------- -->I=>
--  g1 |- \x.e => Ea -> Eb
infer g1 e@(LamE v e2) = runInfer "-->I=>" g1 e $ do
  a <- newvar
  b <- newvar
  let ann = AnnG (VarE v) a
      g' = g1 +> a +> b +> ann
  (g'', t) <- check g' e2 b
  case lookupE (VarE v) g'' of
    (Just a') -> do
      g2 <- cut ann g''
      return (g2, FunT a' t)
    Nothing -> throwError UnknownError

--  g1 |- e1 => A -| g2
--  g2 |- [g2]A o e2 =>> C -| g3
-- ----------------------------------------- -->E
--  g1 |- e1 e2 => C -| g3
infer g1 e@(AppE e1 e2) = runInfer "-->E" g1 e $ do
  (g2, a) <- infer g1 e1
  derive g2 e2 (apply g2 a)
--  g1 |- A
--  g1 |- e <= A -| g2
-- ----------------------------------------- Anno
--  g1 |- (e:A) => A -| g2
infer g e1@(AnnE e@(VarE _) t) = runInfer "Anno" g e1 $ do
  -- This is a bit questionable. If a single variable is annotated, e.g.
  -- `x::Int`, and is not declared, this would normally raise an
  -- UnboundVariable error. However, it is convenient for testing purposes, and
  -- also for Morloc where functions are imported as black boxes from other
  -- langugaes, to be able to simply declare a type as an axiom. Perhaps I
  -- should add dedicated syntax for axiomatic type declarations?
  case lookupE e g of
    (Just _) -> do
      check g e t
      return (g, t)
    Nothing -> return (g, t)
infer g e1@(AnnE e t) = runInfer "Anno" g e1 $ do
  (g, t') <- check g e t
  return (g, t)


-- | Pattern matches against each type
check :: Gamma -> Expr -> Type -> Stack (Gamma, Type)
--
-- ----------------------------------------- 1l
--  g |- () <= 1 -| g
check g UniE UniT = runCheck "1l" g UniE UniT  $ do
  return (g, UniT)
check g e UniT = runCheck "1l-error" g e UniT $ do
  throwError TypeMismatch
--  g1,x:A |- e <= B -| g2,x:A,g3
-- ----------------------------------------- -->I
--  g1 |- \x.e <= A -> B -| g2
check g r1@(LamE v e) r2@(FunT a b) = runCheck "-->I" g r1 r2 $ do
  -- define x:A
  let ann = AnnG (VarE v) a
  -- check that e has the expected output type
  (g', t') <- check (g +> ann) e b
  -- ignore the trailing context and (x:A), since it is out of scope
  g2 <- cut ann g'
  return (g2, t')
--  g1,x |- e <= A -| g2,x,g3
-- ----------------------------------------- Forall.I
--  g1 |- e <= Forall x.A -| g2
check g1 e r2@(Forall x a) = runCheck "Forall.I" g1 e r2 $ do
  (g', t') <- check (g1 +> VarG x) e a
  g2 <- cut (VarG x) g'
  return (g2, t')
--  g1 |- e => A -| g2
--  g2 |- [g2]A <: [g2]B -| g3
-- ----------------------------------------- Sub
--  g1 |- e <= B -| g3
check g1 e b = runCheck "Sub" g1 e b $ do
  (g2, a) <- infer g1 e
  g3 <- subtype (apply g2 a) (apply g2 b) g2
  return (g3, apply g3 a)


derive :: Gamma -> Expr -> Type -> Stack (Gamma, Type)
--  g1 |- e <= A -| g2
-- ----------------------------------------- -->App
--  g1 |- A->C o e =>> C -| g2
derive g e t@(FunT a b) = runDerive "-->App" g e t $ do
  (g', t) <- check g e a
  return (g', apply g' b)
--  g1,Ea |- [Ea/a]A o e =>> C -| g2
-- ----------------------------------------- Forall App
--  g1 |- Forall x.A o e =>> C -| g2
derive g e t'@(Forall x t) = runDerive "ForallApp" g e t' $ do
  derive (g +> ExistG x) e (substitute x t)
--  g1[Ea2, Ea1, Ea=Ea1->Ea2] |- e <= Ea1 -| g2
-- ----------------------------------------- EaApp
--  g1[Ea] |- Ea o e =>> Ea2 -| g2
derive g e t'@(ExistT v) = runDerive "EaApp" g e t' $ do
  a <- newvar
  b <- newvar
  let g' = g +> a +> b +> SolvedG v (FunT a b)
  check g' e a
derive g e t = runDerive "unexpected" g e t $ do
  throwError NonFunctionDerive
