module Xi.Data
(
    Stack
  , Expr(..)
  , EVar(..)
  , TVar(..)
  , Type(..)
  , Gamma
  , GammaIndex(..)
  , cut
  , (+>)
  , TypeError(..)
  , access1
  , access2
  , ann
  , lookupT
  , lookupE
  , throwError
  , runStack
  , index
  -- * State manipulation
  , newvar
  -- * Config handling
  , verbosity
) where

import qualified Data.List as DL
import Control.Monad.Except (throwError)
import qualified Control.Monad.Except as ME
import qualified Control.Monad.State as MS
import qualified Control.Monad.Writer as MW
import qualified Control.Monad.Reader as MR
import qualified Control.Monad.Identity as MI
import qualified Control.Monad as CM
import qualified Data.Text as T
import qualified Test.QuickCheck as QC

type GeneralStack c e l s a = MR.ReaderT c (ME.ExceptT e (MW.WriterT l (MS.StateT s MI.Identity))) a
type Stack a = GeneralStack StackConfig TypeError [T.Text] StackState a

-- | currently I do nothing with the Reader and Writer monads, but I'm leaving
-- them in for now since I will need them when I plug this all into Morloc.
runStack :: Stack a -> Int -> (Either TypeError a, [T.Text])
runStack e verbosity'
  = fst
  . MI.runIdentity
  . flip MS.runStateT emptyState
  . MW.runWriterT
  . ME.runExceptT
  . MR.runReaderT e
  $ StackConfig verbosity'
         

type Gamma = [GammaIndex]
newtype EVar = EV T.Text deriving(Show, Eq, Ord)
newtype TVar = TV T.Text deriving(Show, Eq, Ord)

data StackState = StackState {
      stateVar :: Int
  } deriving(Ord, Eq, Show)
emptyState = StackState 0

data StackConfig = StackConfig {
      configVerbosity :: Int 
  }

verbosity :: Stack Int
verbosity = MR.asks configVerbosity

-- | A context, see Dunfield Figure 6
data GammaIndex
  = VarG TVar
  -- ^ (G,a)
  | AnnG Expr Type
  -- ^ (G,x:A) looked up in the (Var) and cut in (-->I)
  | ExistG TVar
  -- ^ (G,a^) unsolved existential variable
  | SolvedG TVar Type
  -- ^ (G,a^=t) Store a solved existential variable
  | MarkG TVar
  -- ^ (G,>a^) Store a type variable marker bound under a forall
  deriving(Ord, Eq, Show)

-- | Terms, see Dunfield Figure 1
data Expr
  = UniE
  -- ^ (())
  | VarE EVar 
  -- ^ (x)
  | ListE [Expr]
  -- ^ [e]
  | LamE EVar Expr
  -- ^ (\x -> e)
  | AppE Expr Expr
  -- ^ (e e)
  | AnnE Expr Type
  -- ^ (e : A)
  | IntE Integer | NumE Double | LogE Bool | StrE T.Text 
  -- ^ primitives
  | Declaration EVar Expr Expr
  -- ^ x=e1; e2
  | Signature EVar Type Expr
  -- ^ x :: A; e
  deriving(Show, Ord, Eq)

-- | Types, see Dunfield Figure 6
data Type
  = UniT
  -- ^ (1)
  | VarT TVar
  -- ^ (a)
  | ExistT TVar
  -- ^ (a^) will be solved into one of the other types
  | Forall TVar Type
  -- ^ (Forall a . A)
  | FunT Type Type
  -- ^ (A->B)
  | ArrT TVar [Type]
  -- ^ f [Type]
  deriving(Show, Ord, Eq)

data TypeError
  = UnknownError
  | SubtypeError Type Type
  | ExistentialError
  | BadExistentialCast
  | AccessError T.Text
  | NonFunctionDerive
  | UnboundVariable EVar
  | OccursCheckFail
  | EmptyCut
  | TypeMismatch
  | UnexpectedPattern Expr Type
  | ToplevelRedefinition
  | UnkindJackass
  | NoAnnotationFound
  | OtherError T.Text
  deriving(Show, Ord, Eq)

(+>) :: Indexable a => Gamma -> a -> Gamma
(+>) xs x = (index x):xs

-- | remove context up to a marker
cut :: GammaIndex -> Gamma -> Stack Gamma
cut _ [] = throwError EmptyCut
cut i (x:xs)
  | i == x = return xs
  | otherwise = cut i xs

-- | Look up a type annotated expression
lookupE :: Expr -> Gamma -> Maybe Type
lookupE _ [] = Nothing
lookupE e ((AnnG e' t):gs)
  | e == e' = Just t
  | otherwise = lookupE e gs
lookupE e (_:gs) = lookupE e gs

-- | Look up a solved existential type variable
lookupT :: TVar -> Gamma -> Maybe Type
lookupT _ [] = Nothing
lookupT v ((SolvedG v' t):gs)
  | v == v' = Just t
  | otherwise = lookupT v gs
lookupT v (_:gs) = lookupT v gs

access1 :: Indexable a => a -> Gamma -> Maybe (Gamma, GammaIndex, Gamma)
access1 gi gs = case DL.elemIndex (index gi) gs of
  (Just 0) -> Just ([], head gs, tail gs)
  (Just i) -> Just (take i gs, gs !! i, drop (i+1) gs)
  _ -> Nothing

access2
  :: (Indexable a)
  => a -> a -> Gamma -> Maybe (Gamma, GammaIndex, Gamma, GammaIndex, Gamma)
access2 lgi rgi gs
  = case access1 lgi gs of
    Just (ls, x, rs) -> case access1 rgi rs of
      Just (ls', y, rs') -> Just (ls, x, ls', y, rs')
      _ -> Nothing
    _ -> Nothing

ann :: Expr -> Type -> Expr
ann (AnnE e _) t = AnnE e t 
ann e@(Declaration _ _ _) _ = e
ann e@(Signature _ _ _) _ = e
ann e t = AnnE e t

newvar :: Stack Type
newvar = do
  s <- MS.get 
  let v = newvars !! stateVar s
  MS.put $ s {stateVar = stateVar s + 1}
  return (ExistT $ TV v)
  where
    newvars = zipWith (\x y -> T.pack (x ++ show y)) (repeat "t") ([0..] :: [Integer])

class Indexable a where
  index :: a -> GammaIndex

instance Indexable GammaIndex where
  index = id

instance Indexable Type where
  index (ExistT t) = ExistG t 
  index _ = error "Can only index ExistT"

instance Indexable Expr where
  index (AnnE x t) = AnnG x t
  index _ = error "Can only index AnnE"

instance QC.Arbitrary Type where
  arbitrary = arbitraryType 3 []

  shrink (UniT) = [VarT (TV "X")]
  shrink (VarT (TV "X")) = []
  shrink (VarT _) = [VarT (TV "X")]
  shrink (ExistT _) = [VarT (TV "X")]
  shrink (Forall v t) = QC.shrink t ++ [t] ++ [Forall v t' | t' <- QC.shrink t]
  shrink (FunT t1 t2)
    =  QC.shrink t1
    ++ QC.shrink t2
    ++ [t1,t2]
    ++ [FunT t1' t2' | (t1', t2') <- QC.shrink (t1, t2) ]
    ++ [FunT t1' t2  | t1' <- QC.shrink t1 ]
    ++ [FunT t1  t2' | t2' <- QC.shrink t2 ]
  shrink (ArrT _ []) = [] -- this expression should not be generated
  shrink (ArrT v@(TV "L") [p1,p2,p3])
    = [VarT (TV "X")]
    ++ QC.shrink p1
    ++ QC.shrink p2
    ++ QC.shrink p3
    ++ QC.shrink (ArrT (TV "K") [p1,p2])
    ++ QC.shrink (ArrT (TV "K") [p1,p3])
    ++ QC.shrink (ArrT (TV "K") [p2,p3])
    ++ [ArrT v [p1',p2',p3'] | (p1',p2',p3') <- QC.shrink (p1,p2,p3)]
  shrink (ArrT v@(TV "K") [p1,p2])
    = [VarT (TV "X")]
    ++ QC.shrink p1
    ++ QC.shrink p2
    ++ QC.shrink (ArrT (TV "J") [p1])
    ++ QC.shrink (ArrT (TV "J") [p2])
    ++ [ArrT v [p1',p2'] | (p1',p2') <- QC.shrink (p1,p2)]
  shrink (ArrT (TV "J") [p])
    = [VarT (TV "X")]
    ++ QC.shrink p
  shrink (ArrT v (p:ps))
    = [VarT (TV "X")]
    ++ [ArrT v (p':ps') | p' <- QC.shrink p, (ArrT _ ps') <- QC.shrink (ArrT v ps)]
    ++ [ArrT v (p:ps') | (ArrT _ ps') <- QC.shrink (ArrT v ps)]

arbitraryType :: Int -> [TVar] -> QC.Gen Type
arbitraryType depth vs = QC.oneof [
      arbitraryType' depth vs
    , Forall <$> pure (newvar' vs) <*> arbitraryType depth (newvar' vs : vs)
  ]
  where
    variables = [1..] >>= flip CM.replicateM ['a'..'z']
    newvar' vs' = TV (T.pack $ variables !! length vs')

arbitraryType' :: Int -> [TVar] -> QC.Gen Type
arbitraryType' 0 vs = atomicType vs
arbitraryType' depth vs = QC.oneof [
      atomicType vs 
    , FunT <$> arbitraryType' (depth-1) vs <*> arbitraryType' (depth-1) vs
    , QC.elements [ExistT (TV "e1"), ExistT (TV "e2"), ExistT (TV "e3")]
    , QC.frequency [
          (3, arbitraryArrT (depth-1) vs (TV "J") 1)
        , (2, arbitraryArrT (depth-1) vs (TV "K") 2)
        , (1, arbitraryArrT (depth-1) vs (TV "L") 3)
      ]
  ]

atomicType :: [TVar] -> QC.Gen Type
atomicType [] = QC.elements [VarT (TV "A"), VarT (TV "B"), VarT (TV "C")]
atomicType vs = QC.oneof [
      atomicType []
    , QC.elements (map (\v -> VarT v) vs)
  ]
arbitraryArrT :: Int -> [TVar] -> TVar -> Int -> QC.Gen Type
arbitraryArrT depth vs v arity = ArrT <$> pure v <*> CM.replicateM arity (arbitraryType' depth vs)

instance QC.Arbitrary Expr where
  arbitrary = undefined
  shrink = undefined

instance QC.Arbitrary GammaIndex where
  arbitrary = undefined
  shrink = undefined

instance QC.Arbitrary TVar where
  arbitrary = QC.elements [TV "a", TV "b", TV "c"]
  shrink _ = []

instance QC.Arbitrary EVar where
  arbitrary = undefined
  shrink = undefined
