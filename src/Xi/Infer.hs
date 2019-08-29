module Xi.Infer (
    typecheck
  , subtype
  , generalize
  , substitute
  , apply
) where

import Xi.Data
import Control.Monad.Trans (liftIO)
import Data.Text.Prettyprint.Doc
import Control.Monad (replicateM)
import qualified Data.Text as T
import qualified Data.Set as Set

typecheck :: Expr -> Stack Expr
typecheck e = fmap (generalizeE . (\(_, _, e') -> e')) (infer [] e)

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
    run1 v d'
      | v < 2 = return ()
      | otherwise = do
        liftIO . print $ pretty (take d' $ repeat '>') <+> s
        mapM writeArg args
        return ()
    run2 v d'
      | v < 2 = return ()
      | otherwise = do
        liftIO . print $ pretty (take d' $ repeat '<') <+> s
    run3 v x'
      | v < 2 = return ()
      | otherwise = do
        liftIO . print $ "  return:" <+> pretty x'

writeArg :: (Doc', Doc') -> Stack ()
writeArg (name, arg) = do
  liftIO . print $ "  " <> name <> ":" <+> arg

runSubtype :: Doc' -> Type -> Type -> Gamma -> Stack Gamma -> Stack Gamma
runSubtype s t1 t2 g x
  = run ("subtype " <> s) [("t1", pretty t1), ("t2", pretty t2), ("g", pretty g)] x

runInstantiate :: Doc' -> Type -> Type -> Gamma -> Stack Gamma -> Stack Gamma
runInstantiate s t1 t2 g x
  = run ("instantiate " <> s) [("ta", pretty t1), ("tb", pretty t2), ("g", pretty g)] x

runInfer :: Doc' -> Gamma -> Expr -> Stack (Gamma, Type, Expr) -> Stack (Gamma, Type, Expr)
runInfer s g e x = do
  run ("infer " <> s) [("g", pretty g), ("e", pretty (show e))] x

runCheck :: Doc' -> Gamma -> Expr -> Type -> Stack (Gamma, Type, Expr) -> Stack (Gamma, Type, Expr)
runCheck s g e t x
  = run ("check " <> s) [("g", pretty g), ("e", pretty (show e)), ("t", pretty t)] x

runDerive :: Doc' -> Gamma -> Expr -> Type -> Stack (Gamma, Type, Expr) -> Stack (Gamma, Type, Expr)
runDerive s g e t x
  = run ("synthesize " <> s) [("g", pretty g), ("e", pretty (show e)), ("t", pretty t)] x

generalize :: Type -> Type
generalize t = generalize' existentialMap t
  where 

    generalize' :: [(TVar, TVar)] -> Type -> Type
    generalize' [] t' = t'
    generalize' ((e,r):xs) t' = generalize' xs (generalizeOne e r t')

    existentialMap
      = zip
        (Set.toList (findExistentials t))
        (map (TV . T.pack) variables)

    variables = [1..] >>= flip replicateM ['a'..'z']

    findExistentials :: Type -> Set.Set TVar
    findExistentials UniT = Set.empty
    findExistentials (VarT _) = Set.empty
    findExistentials (ExistT v) = Set.singleton v
    findExistentials (Forall v t') = Set.delete v (findExistentials t')
    findExistentials (FunT t1 t2) = Set.union (findExistentials t1) (findExistentials t2)
    findExistentials (ArrT _ ts) = Set.unions (map findExistentials ts)

    generalizeOne :: TVar -> TVar -> Type -> Type
    generalizeOne v0 r t0 = Forall r (f v0 t0) where
      f :: TVar -> Type -> Type
      f v t1@(ExistT v')
        | v == v' = VarT r
        | otherwise = t1
      f v (FunT t1 t2) = FunT (f v t1) (f v t2)
      f v t1@(Forall x t2)
        | v /= x = Forall x (f v t2)
        | otherwise = t1
      f v (ArrT v' xs) = ArrT v' (map (f v) xs)
      f _ t1 = t1

generalizeE :: Expr -> Expr
generalizeE (ListE xs) = ListE (map generalizeE xs)
generalizeE (LamE v e) = LamE v (generalizeE e)
generalizeE (AppE e1 e2) = AppE (generalizeE e1) (generalizeE e2)
generalizeE (AnnE e t) = ann (generalizeE e) (generalize t)
generalizeE (Declaration v e1 e2) = Declaration v (generalizeE e1) (generalizeE e2)
generalizeE (Signature v t e) = Signature v (generalize t) (generalizeE e)
generalizeE e = e


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

-- | Ensure a given type variable is not free within a given type
occursCheck :: Type -> TVar -> Stack ()
occursCheck UniT _ = return ()
occursCheck (VarT v') v 
  | v' == v = throwError OccursCheckFail
  | otherwise = return ()
occursCheck (FunT t1 t2) v = do
  occursCheck t1 v
  occursCheck t2 v
occursCheck (Forall v' t) v
  | v' == v = return () -- variable is bound, we are done
  | otherwise = occursCheck t v -- else recurse
occursCheck (ExistT v') v
  | v' == v = throwError OccursCheckFail -- existentials count
  | otherwise = return ()
occursCheck (ArrT _ []) _ = return ()
occursCheck (ArrT v' ts) v
  | v' == v = throwError OccursCheckFail
  | otherwise = mapM_ (flip occursCheck $ v) ts


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
subtype UniT UniT g = runSubtype "Unit" UniT UniT g $ do
  return g
--
-- ----------------------------------------- <:Var
--  G[a] |- a <: a -| G[a]
subtype t1@(VarT a1) t2@(VarT a2) g = runSubtype "<:Var" t1 t2 g $ do
  if (a1 == a2)
  then return g
  else throwError $ SubtypeError t1 t2
subtype a@(ExistT a1) b@(ExistT a2) g
  --
  -- ----------------------------------------- <:Exvar
  --  G[E.a] |- Ea <: Ea -| G[E.a]
  | a1 == a2 = runSubtype "<:Exvar" a b g $ return g
  --
  -- ----------------------------------------- <:InstantiateL/<:InstantiateR
  --  G[E.a] |- Ea <: Ea -| G[E.a]
  | otherwise = runSubtype "<:InstantiateL" a b g $ do
      -- formally, an `Ea notin FV(G)` check should be done here, but since the
      -- types involved are all existentials, it will always pass, so I omit
      -- it.
      instantiate a b g 
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
    compareArr (t1':ts1') (t2':ts2') g' = do
      g'' <- subtype t1' t2' g'
      compareArr ts1' ts2' g''
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
  throwError $ SubtypeError a b 



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
infer g e@UniE = runInfer "Unit=>" g e $ do
  return (g, UniT, ann UniE UniT) 
infer g e@(NumE _) = runInfer "Num=>" g e $ do
  let t = VarT (TV "Num")
  return (g, t, ann e t)
infer g e@(IntE _) = runInfer "Int=>" g e $ do
  let t = VarT (TV "Int")
  return (g, t, ann e t)
infer g e@(StrE _) = runInfer "Str=>" g e $ do
  let t = VarT (TV "Str")
  return (g, t, ann e t)
infer g e@(LogE _) = runInfer "Log=>" g e $ do
  let t = VarT (TV "Bool")
  return (g, t, ann e t)

-- ----------------------------------------- Declaration=>
infer g e@(Declaration v e1 e2) = runInfer "Declaration=>" g e $ do
  occursCheckExpr g v
  (_, t1', e1') <- infer g e1
  (g'', t2', e2') <- infer (g +> AnnG (VarE v) (generalize t1')) e2
  return (g'', t2', Declaration v (generalizeE e1') e2')

-- ----------------------------------------- Signature=>
infer g e@(Signature v t e2) = runInfer "Signature=>" g e $ do
  (g', t', e2') <- infer (g +> AnnG (VarE v) t) e2
  return $ (g', t', Signature v t e2')

--  (x:A) in g
-- ------------------------------------------- Var
--  g |- x => A -| g
infer g e@(VarE v) = runInfer "Var" g e $ do
  case lookupE e g of
    (Just t) -> return (g, t, ann e t)
    Nothing -> throwError (UnboundVariable v)

--  g1,Ea,Eb,x:Ea |- e <= Eb -| g2,x:Ea,g3
-- ----------------------------------------- -->I=>
--  g1 |- \x.e => Ea -> Eb -| g2
infer g1 e@(LamE v e2) = runInfer "-->I=>" g1 e $ do
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
infer g1 e@(AppE e1 e2) = runInfer "-->E" g1 e $ do
  (g2, a, e1') <- infer g1 e1
  (g3, c, e2') <- derive g2 e2 (apply g2 a)
  e3 <- applyConcrete e1' e2' c
  return (g3, c, e3)

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
    (Just _) -> check g e t
    Nothing -> return (g, t, e1)
infer g e1@(AnnE e t) = runInfer "Anno" g e1 $ do
  check g e t

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
check g UniE UniT = runCheck "1l" g UniE UniT  $ do
  return (g, UniT, ann UniE UniT)
check g e UniT = runCheck "1l-error" g e UniT $ do
  throwError TypeMismatch
--  g1,x:A |- e <= B -| g2,x:A,g3
-- ----------------------------------------- -->I
--  g1 |- \x.e <= A -> B -| g2
check g r1@(LamE v e) r2@(FunT a b) = runCheck "-->I" g r1 r2 $ do
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
check g1 e r2@(Forall x a) = runCheck "Forall.I" g1 e r2 $ do
  (g', _, e') <- check (g1 +> VarG x) e a
  g2 <- cut (VarG x) g'
  let t'' = apply g2 r2
  return (g2, t'', ann e' t'')
--  g1 |- e => A -| g2
--  g2 |- [g2]A <: [g2]B -| g3
-- ----------------------------------------- Sub
--  g1 |- e <= B -| g3
check g1 e b = runCheck "Sub" g1 e b $ do
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
derive g e t@(FunT a b) = runDerive "-->App" g e t $ do
  (g', _, e') <- check g e a
  return (g', apply g' b, e')

--  g1,Ea |- [Ea/a]A o e =>> C -| g2
-- ----------------------------------------- Forall App
--  g1 |- Forall x.A o e =>> C -| g2
derive g e t@(Forall x s) = runDerive "ForallApp" g e t $ do
  derive (g +> ExistG x) e (substitute x s)

--  g1[Ea2, Ea1, Ea=Ea1->Ea2] |- e <= Ea1 -| g2
-- ----------------------------------------- EaApp
--  g1[Ea] |- Ea o e =>> Ea2 -| g2
derive g e t'@(ExistT v) = runDerive "EaApp" g e t' $ do
  a <- newvar
  b <- newvar
  let g' = g +> a +> b +> SolvedG v (FunT a b)
  (g'', _, _) <- check g' e a
  return (g'', apply g'' b, applyE g'' e)

derive g e t = runDerive "unexpected" g e t $ do
  throwError NonFunctionDerive
