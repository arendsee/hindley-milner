module Xi.Infer (
    typecheck
  , subtype
  , substitute
  , apply
  , applyE
  , free
  , infer
) where

import Xi.Data
import Control.Monad (replicateM)
import qualified Data.Text as T
import qualified Data.Set as Set

typecheck :: Expr -> Stack Expr
typecheck e = fmap (generalizeE . (\(_, _, e') -> e')) (infer [] e)


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
substitute v (ArrT v' ts) = ArrT v' (map (substitute v) ts)
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
apply g (ArrT v ts) = ArrT v (map (apply g) ts) 

applyE :: Gamma -> Expr -> Expr
applyE g (ListE xs) = ListE (map (applyE g) xs)
applyE g (LamE v e) = LamE v (applyE g e)
applyE g (AppE e1 e2) = AppE (applyE g e1) (applyE g e2)
applyE g (AnnE e t) = ann (applyE g e) (apply g t)
applyE g (Declaration v e1 e2) = Declaration v (applyE g e1) (applyE g e2)
applyE g (Signature v t e) = Signature v (apply g t) (applyE g e)
applyE _ e@(VarE _) = e
applyE _ e@(IntE _) = e
applyE _ e@(NumE _) = e
applyE _ e@(StrE _) = e
applyE _ e@(LogE _) = e
applyE _ UniE = UniE

occursCheck :: Type -> Type -> Stack()
occursCheck t1 t2 = case Set.member t1 (free t2) of
  True -> throwError OccursCheckFail
  False -> return()

free :: Type -> Set.Set Type
free UniT = Set.empty
free v@(VarT _) = Set.singleton v
free v@(ExistT _) = Set.singleton v
free (FunT t1 t2) = Set.union (free t1) (free t2)
free (Forall v t) = Set.delete (VarT v) (free t)
free (ArrT _ xs) = Set.unions (map free xs)

occursCheckExpr :: Gamma -> EVar -> Stack ()
occursCheckExpr [] _ = return ()
occursCheckExpr ((AnnG (VarE v') _):gs) v
  | v' == v = throwError ToplevelRedefinition
  | otherwise = occursCheckExpr gs v
occursCheckExpr _ _ = return ()

-- | type 1 is more polymorphic than type 2 (Dunfield Figure 9)
subtype :: Type -> Type -> Gamma -> Stack Gamma
--
-- ----------------------------------------- Unit
--  G |- 1 <: 1 -| G
subtype UniT UniT g = return g
--
-- ----------------------------------------- <:Var
--  G[a] |- a <: a -| G[a]
subtype t1@(VarT a1) t2@(VarT a2) g = do
  if (a1 == a2)
  then return g
  else throwError $ SubtypeError t1 t2
subtype a@(ExistT a1) b@(ExistT a2) g
  --
  -- ----------------------------------------- <:Exvar
  --  G[E.a] |- Ea <: Ea -| G[E.a]
  | a1 == a2 = return g
  --
  -- ----------------------------------------- <:InstantiateL/<:InstantiateR
  --  G[E.a] |- Ea <: Ea -| G[E.a]
  | otherwise =
      -- formally, an `Ea notin FV(G)` check should be done here, but since the
      -- types involved are all existentials, it will always pass, so I omit
      -- it.
      instantiate a b g 
--  g1 |- B1 <: A1 -| g2
--  g2 |- [g2]A2 <: [g2]B2 -| g3
-- ----------------------------------------- <:-->
--  g1 |- A1 -> A2 <: B1 -> B2 -| g3
subtype (FunT a1 a2) (FunT b1 b2) g1 = do
  -- function subtypes are *contravariant* with respect to the input, that is,
  -- the subtypes are reversed so we have b1<:a1 instead of a1<:b1.
  g2 <- subtype b1 a1 g1
  subtype (apply g2 a2) (apply g2 b2) g2
subtype (ArrT v1 []) (ArrT v2 []) g = subtype (VarT v1) (VarT v2) g
subtype (ArrT v1 vs1) (ArrT v2 vs2) g = do
  subtype (VarT v1) (VarT v2) g
  compareArr vs1 vs2 g
  where
    compareArr :: [Type] -> [Type] -> Gamma -> Stack Gamma
    compareArr [] [] g' = return g'
    compareArr (t1':ts1') (t2':ts2') g' = do
      g'' <- subtype t1' t2' g'
      compareArr ts1' ts2' g''
    compareArr _ _ _ = throwError UnkindJackass

--  g1 |- A1 <: B1
-- ----------------------------------------- <:App
--  g1 |- A1 A2 <: B1 B2 -| g2
--  unparameterized types are the same as VarT, so subtype on that instead
--  Ea not in FV(a)
--  g1[Ea] |- A <=: Ea -| g2
-- ----------------------------------------- <:InstantiateR
--  g1[Ea] |- A <: Ea -| g2
subtype a b@(ExistT _) g = occursCheck a b >> instantiate a b g 

--  Ea not in FV(a)
--  g1[Ea] |- Ea <=: A -| g2
-- ----------------------------------------- <:InstantiateL
--  g1[Ea] |- Ea <: A -| g2
subtype a@(ExistT _) b g = occursCheck b a >> instantiate a b g 

--  g1,>Ea,Ea |- [Ea/x]A <: B -| g2,>Ea,g3
-- ----------------------------------------- <:ForallL
--  g1 |- Forall x . A <: B -| g2
subtype (Forall x a) b g = subtype (substitute x a) b (g +> MarkG x +> ExistG x) >>= cut (MarkG x)

--  g1,a |- A :> B -| g2,a,g3
-- ----------------------------------------- <:ForallR
--  g1 |- A <: Forall a. B -| g2
subtype a (Forall v b) g = subtype a b (g +> VarG v) >>= cut (VarG v)

subtype a b _ = throwError $ SubtypeError a b 


-- | Dunfield Figure 10 -- type-level structural recursion
instantiate :: Type -> Type -> Gamma -> Stack Gamma

--  g1[Ea2, Ea1, Ea=Ea1->Ea2] |- A1 <=: Ea1 -| g2
--  g2 |- Ea2 <=: [g2]A2 -| g3
-- ----------------------------------------- InstLArr
--  g1[Ea] |- Ea <=: A1 -> A2 -| g3
instantiate ta@(ExistT v) (FunT t1 t2) g1 = do
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
instantiate (FunT t1 t2) tb@(ExistT v) g1 = do
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
instantiate ta@(ExistT _) (Forall v2 t2) g1 =
  instantiate ta t2 (g1 +> VarG v2) >>= cut (VarG v2)

-- InstLReach or instRReach -- each rule eliminates an existential
-- Replace the rightmost with leftmost (G[a][b] --> L,a,M,b=a,R)
-- WARNING: be careful here, since the implementation adds to the front and the
-- formal syntax adds to the back. Don't change anything in the function unless
-- you really know what you are doing and have tests to confirm it.
instantiate ta@(ExistT v1) tb@(ExistT v2) g1 = do
  _ <- return ()
  case access2 ta tb g1 of
    -- InstLReach
    (Just (ls, _, ms, x, rs)) -> return $ ls <> (SolvedG v1 tb:ms) <> (x:rs)
    Nothing -> case access2 tb ta g1 of
      -- InstRReach
      (Just (ls, _, ms, x, rs)) -> return $ ls <> (SolvedG v2 ta:ms) <> (x:rs)
      Nothing -> return g1

--  g1[Ea],>Eb,Eb |- [Eb/x]B <=: Ea -| g2,>Eb,g3
-- ----------------------------------------- InstRAllL
--  g1[Ea] |- Forall x. B <=: Ea -| g2
instantiate (Forall x b) tb@(ExistT _) g1 = do
  instantiate
      (substitute x b)             -- [Eb/x]B
      tb                           -- Ea
      (g1 +> MarkG x +> ExistG x)  -- g1[Ea],>Eb,Eb
  >>= cut (MarkG x)
--  g1 |- t
-- ----------------------------------------- InstRSolve
--  g1,Ea,g2 |- t <=: Ea -| g1,Ea=t,g2
instantiate ta tb@(ExistT v) g1 =
  case access1 tb g1 of
    (Just (ls, _, rs)) -> return $ ls ++ (SolvedG v ta):rs
    Nothing -> case access1 (SolvedG v ta) g1 of
      (Just _) -> return g1
      Nothing -> error "error in InstRSolve"
--  g1 |- t
-- ----------------------------------------- instLSolve
--  g1,Ea,g2 |- Ea <=: t -| g1,Ea=t,g2
instantiate ta@(ExistT v) tb g1 = do
  case access1 ta g1 of
    (Just (ls, _, rs)) -> return $ ls ++ (SolvedG v tb):rs
    Nothing -> case access1 (SolvedG v tb) g1 of
      (Just _) -> return g1
      Nothing -> error "error in InstLSolve"
-- accessWith
--   :: (Show a, Indexable a)
--   => (GammaIndex -> GammaIndex) -> a -> Gamma -> Stack Gamma
-- accessWith f gi gs = case access1 gi gs of
--   (Just (ls, x, rs)) -> return $ ls <> (f x:rs)
--   Nothing -> throwError $ AccessError ("Cannot find " <> show' (index gi) <> " in " <> show' gs)

-- bad
instantiate _ _ g = do
  return g

applyConcrete :: Expr -> Expr -> Type -> Stack Expr
applyConcrete (AnnE e1 _) e2@(AnnE _ a) c = return $ AnnE (AppE (AnnE e1 (FunT a c)) e2) c
applyConcrete _ _ _ = throwError $ OtherError "Expected annotated types in applyConcrete"

infer
  :: Gamma
  -> Expr -- ^ A subexpression from the original expression
  -> Stack (
      Gamma
    , Type -- The return type
    , Expr -- The annotated expression
  )
-- --
-- ----------------------------------------- <primitive>
--  g |- <primitive expr> => <primitive type> -| g
-- --
infer g UniE = return (g, UniT, ann UniE UniT) 
-- Num=>
infer g e@(NumE _) = return (g, t, ann e t) where
  t = VarT (TV "Num")
-- Int=>
infer g e@(IntE _) = return (g, t, ann e t) where
  t = VarT (TV "Int")
-- Str=> 
infer g e@(StrE _) = return (g, t, ann e t) where
  t = VarT (TV "Str")
-- Log=> 
infer g e@(LogE _) = return (g, t, ann e t) where
  t = VarT (TV "Bool")
-- Declaration=>
infer g (Declaration v e1 e2) = do
  occursCheckExpr g v
  (_, t1', e1') <- infer g e1
  (g'', t2', e2') <- infer (g +> AnnG (VarE v) (generalize t1')) e2
  return (g'', t2', Declaration v (generalizeE e1') e2')
-- Signature=>
infer g (Signature v t e2) = do
  (g', t', e2') <- infer (g +> AnnG (VarE v) t) e2
  return $ (g', t', Signature v t e2')

--  (x:A) in g
-- ------------------------------------------- Var
--  g |- x => A -| g
infer g e@(VarE v) = do
  case lookupE e g of
    (Just t) -> return (g, t, ann e t)
    Nothing -> throwError (UnboundVariable v)

--  g1,Ea,Eb,x:Ea |- e <= Eb -| g2,x:Ea,g3
-- ----------------------------------------- -->I=>
--  g1 |- \x.e => Ea -> Eb -| g2
infer g1 (LamE v e2) = do
  a <- newvar
  b <- newvar
  let anng = AnnG (VarE v) a
      g' = g1 +> a +> b +> anng
  (g'', t, e2') <- check g' e2 b
  case lookupE (VarE v) g'' of
    (Just a') -> do
      g2 <- cut anng g''
      let t' = FunT a' t
      return (g2, t', ann (LamE v e2') t')
    Nothing -> throwError UnknownError

--  g1 |- e1 => A -| g2
--  g2 |- [g2]A o e2 =>> C -| g3
-- ----------------------------------------- -->E
--  g1 |- e1 e2 => C -| g3
infer g1 (AppE e1 e2) = do
  (g2, a, e1') <- infer g1 e1
  (g3, c, e2') <- derive g2 e2 (apply g2 a)
  e3 <- applyConcrete e1' e2' c
  return (g3, c, e3)

--  g1 |- A
--  g1 |- e <= A -| g2
-- ----------------------------------------- Anno
--  g1 |- (e:A) => A -| g2
infer g e1@(AnnE e@(VarE _) t) = do
  -- This is a bit questionable. If a single variable is annotated, e.g.
  -- `x::Int`, and is not declared, this would normally raise an
  -- UnboundVariable error. However, it is convenient for testing purposes, and
  -- also for Morloc where functions are imported as black boxes from other
  -- langugaes, to be able to simply declare a type as an axiom. Perhaps I
  -- should add dedicated syntax for axiomatic type declarations?
  case lookupE e g of
    (Just _) -> check g e t
    Nothing -> return (g, t, e1)
infer g (AnnE e t) = check g e t

infer g e1@(ListE []) = do
  t <- newvar
  let t' = ArrT (TV "List") [t]
  return (g +> t, t', ann e1 t')
infer g e1@(ListE (x:xs)) = do 
  (g', t', _) <- infer g x
  mapM (\x' -> check g x' t') xs 
  let t'' = ArrT (TV "List") [t']
  return (g', t'', ann e1 t'')


-- | Pattern matches against each type
check
  :: Gamma
  -> Expr -- ^ An expression which should be of the type given
  -> Type -- ^ The expected type of the expression
  -> Stack (
      Gamma
    , Type -- The inferred type of the expression
    , Expr -- The annotated expression
  )
--
-- ----------------------------------------- 1l
--  g |- () <= 1 -| g
check g UniE UniT = return (g, UniT, ann UniE UniT)
-- 1l-error
check _ _ UniT = throwError TypeMismatch
--  g1,x:A |- e <= B -| g2,x:A,g3
-- ----------------------------------------- -->I
--  g1 |- \x.e <= A -> B -| g2
check g (LamE v e) (FunT a b) = do
  -- define x:A
  let anng = AnnG (VarE v) a
  -- check that e has the expected output type
  (g', t', e') <- check (g +> anng) e b
  -- ignore the trailing context and (x:A), since it is out of scope
  g2 <- cut anng g'
  let t'' = FunT a t'
  return (g2, t'', ann (LamE v e') t'')
--  g1,x |- e <= A -| g2,x,g3
-- ----------------------------------------- Forall.I
--  g1 |- e <= Forall x.A -| g2
check g1 e r2@(Forall x a) = do
  (g', _, e') <- check (g1 +> VarG x) e a
  g2 <- cut (VarG x) g'
  let t'' = apply g2 r2
  return (g2, t'', ann e' t'')
--  g1 |- e => A -| g2
--  g2 |- [g2]A <: [g2]B -| g3
-- ----------------------------------------- Sub
--  g1 |- e <= B -| g3
check g1 e b = do
  (g2, a, e') <- infer g1 e
  g3 <- subtype (apply g2 a) (apply g2 b) g2
  let a' = apply g3 a
  return (g3, a', ann (applyE g3 e') a')

derive
  :: Gamma
  -> Expr -- the expression that is passed to the function
  -> Type -- the function type
  -> Stack (
        Gamma
      , Type -- @b@, the function output type after context application
      , Expr -- @e@, with type annotation
  )
--  g1 |- e <= A -| g2
-- ----------------------------------------- -->App
--  g1 |- A->C o e =>> C -| g2
derive g e (FunT a b) = do
  (g', _, e') <- check g e a
  return (g', apply g' b, e')

--  g1,Ea |- [Ea/a]A o e =>> C -| g2
-- ----------------------------------------- Forall App
--  g1 |- Forall x.A o e =>> C -| g2
derive g e (Forall x s) = derive (g +> ExistG x) e (substitute x s)

--  g1[Ea2, Ea1, Ea=Ea1->Ea2] |- e <= Ea1 -| g2
-- ----------------------------------------- EaApp
--  g1[Ea] |- Ea o e =>> Ea2 -| g2
derive g e (ExistT v) = do
  a <- newvar
  b <- newvar
  let g' = g +> a +> b +> SolvedG v (FunT a b)
  (g'', _, _) <- check g' e a
  return (g'', apply g'' b, applyE g'' e)

derive _ _ _ = throwError NonFunctionDerive
