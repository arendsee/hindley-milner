module Xi.Data
(
    Stack
  , Expr(..)
  , EVar(..)
  , TVar(..)
  , MVar(..)
  , Type(..)
  , Gamma
  , GammaIndex(..)
  , Module(..)
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
  , generalize
  , generalizeE
  , mapT
  , mapT'
  -- * State manipulation
  , newvar
  , newqul
  -- * pretty printing
  , prettyExpr
  , prettyModule
  , prettyType
  , desc
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
import qualified Data.Set as Set
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Render.Terminal.Internal

data Dag a = Node a [Dag a] deriving(Show, Eq, Ord)

type GeneralStack c e l s a = MR.ReaderT c (ME.ExceptT e (MW.WriterT l (MS.StateT s MI.Identity))) a
type Stack a = GeneralStack StackConfig TypeError [T.Text] StackState a

-- | currently I do nothing with the Reader and Writer monads, but I'm leaving
-- them in for now since I will need them when I plug this all into Morloc.
runStack :: Stack a -> (Either TypeError a, [T.Text])
runStack e
  = fst
  . MI.runIdentity
  . flip MS.runStateT emptyState
  . MW.runWriterT
  . ME.runExceptT
  . MR.runReaderT e
  $ StackConfig 0
         

type Gamma = [GammaIndex]
newtype EVar = EV T.Text deriving(Show, Eq, Ord)
newtype MVar = MV T.Text deriving(Show, Eq, Ord)
newtype TVar = TV T.Text deriving(Show, Eq, Ord)

data StackState = StackState {
      stateVar :: Int
    , stateQul :: Int
  } deriving(Ord, Eq, Show)
emptyState = StackState 0 0

data StackConfig = StackConfig {
      configVerbosity :: Int -- Not currently used
  }

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
  | MarkEG EVar
  deriving(Ord, Eq, Show)

data Module = Module {
    moduleName :: MVar
  , moduleImports :: [(MVar, EVar, Maybe EVar)]
  , moduleExports :: [EVar]
  , moduleBody :: [Expr]
} deriving (Ord, Eq, Show)

-- | Terms, see Dunfield Figure 1
data Expr
  = Signature EVar Type
  -- ^ x :: A; e
  | Declaration EVar Expr
  -- ^ x=e1; e2
  | UniE
  -- ^ (())
  | VarE EVar 
  -- ^ (x)
  | ListE [Expr]
  -- ^ [e]
  | TupleE [Expr]
  -- ^ (e1), (e1,e2), ... (e1,e2,...,en)
  | LamE EVar Expr
  -- ^ (\x -> e)
  | AppE Expr Expr
  -- ^ (e e)
  | AnnE Expr Type
  -- ^ (e : A)
  | IntE Integer | NumE Double | LogE Bool | StrE T.Text 
  -- ^ primitives
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
  | MultipleModuleDeclarations Module
  | BadImport MVar EVar
  | CannotFindModule MVar
  | CyclicDependency
  | CannotImportMain
  deriving(Show, Ord, Eq)

mapT :: (Type -> Type) -> Expr -> Expr
mapT f (LamE v e) = LamE v (mapT f e)
mapT f (ListE es) = ListE (map (mapT f) es)
mapT f (TupleE es) = TupleE (map (mapT f) es)
mapT f (AppE e1 e2) = AppE (mapT f e1) (mapT f e2)
mapT f (AnnE e t) = AnnE (mapT f e) (f t)
mapT f (Declaration v e) = Declaration v (mapT f e)
mapT f (Signature v t) = Signature v (f t)
mapT _ e = e

mapT' :: Monad m => (Type -> m Type) -> Expr -> m Expr
mapT' f (LamE v e) = LamE <$> pure v <*> mapT' f e
mapT' f (ListE es) = ListE <$> mapM (mapT' f) es
mapT' f (TupleE es) = TupleE <$> mapM (mapT' f) es
mapT' f (AppE e1 e2) = AppE <$> mapT' f e1 <*> mapT' f e2
mapT' f (AnnE e t) = AnnE <$> mapT' f e <*> f t
mapT' f (Declaration v e) = Declaration <$> pure v <*> mapT' f e
mapT' f (Signature v t) = Signature <$> pure v <*> f t
mapT' _ e = return e

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
ann e@(Declaration _ _) _ = e
ann e@(Signature _ _) _ = e
ann e t = AnnE e t

generalize :: Type -> Type
generalize t = generalize' existentialMap t where 
  generalize' :: [(TVar, TVar)] -> Type -> Type
  generalize' [] t' = t'
  generalize' ((e,r):xs) t' = generalize' xs (generalizeOne e r t')

  existentialMap
    = zip
      (Set.toList (findExistentials t))
      (map (TV . T.pack) variables)

  variables = [1..] >>= flip CM.replicateM ['a'..'z']

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
generalizeE = mapT generalize

newvar :: Stack Type
newvar = do
  s <- MS.get 
  let v = newvars !! stateVar s
  MS.put $ s {stateVar = stateVar s + 1}
  return (ExistT $ TV v)
  where
    newvars = zipWith (\x y -> T.pack (x ++ show y)) (repeat "t") ([0..] :: [Integer])

newqul :: TVar -> Stack TVar
newqul (TV v) = do
  s <- MS.get
  let v' = TV (v <> "." <> (T.pack . show $ stateQul s)) -- create a new variable such as "a.0"
  MS.put $ s {stateQul = stateQul s + 1}
  return v'


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

typeStyle = SetAnsiStyle {
      ansiForeground  = Just (Vivid, Green) -- ^ Set the foreground color, or keep the old one.
    , ansiBackground  = Nothing             -- ^ Set the background color, or keep the old one.
    , ansiBold        = Nothing             -- ^ Switch on boldness, or don’t do anything.
    , ansiItalics     = Nothing             -- ^ Switch on italics, or don’t do anything.
    , ansiUnderlining = Just Underlined     -- ^ Switch on underlining, or don’t do anything.
  } 

prettyMVar :: MVar -> Doc AnsiStyle
prettyMVar (MV x) = pretty x

prettyModule :: Module -> Doc AnsiStyle
prettyModule m
  =  prettyMVar (moduleName m)
  <+> braces (line <> (indent 4 (prettyBlock m)) <> line)

prettyBlock :: Module -> Doc AnsiStyle
prettyBlock m
  =  vsep (map prettyImport (moduleImports m))
  <> vsep ["export" <+> pretty e <> line | (EV e) <- moduleExports m]
  <> vsep (map prettyExpr (moduleBody m))

prettyImport :: (MVar, EVar, Maybe EVar) -> Doc AnsiStyle
prettyImport (MV m, EV e, Just (EV alias))
  = "from" <+> pretty m <+> "import" <+> pretty e <+> "as" <+> pretty alias <> line
prettyImport (MV m, EV e, Nothing)
  = "from" <+> pretty m <+> "import" <+> pretty e <> line

prettyExpr :: Expr -> Doc AnsiStyle
prettyExpr UniE = "()"
prettyExpr (VarE (EV s)) = pretty s
prettyExpr (LamE (EV n) e) = "\\" <> pretty n <+> "->" <+> prettyExpr e
prettyExpr (AnnE e t) = parens (prettyExpr e <+> "::" <+> prettyGreenType t)
prettyExpr (AppE e1@(LamE _ _) e2) = parens (prettyExpr e1) <+> prettyExpr e2
prettyExpr (AppE e1 e2) = prettyExpr e1 <+> prettyExpr e2
prettyExpr (IntE x) = pretty x
prettyExpr (NumE x) = pretty x
prettyExpr (StrE x) = dquotes (pretty x)
prettyExpr (LogE x) = pretty x
prettyExpr (Declaration (EV v) e) = pretty v <+> "=" <+> prettyExpr e
prettyExpr (Signature (EV v) t) = pretty v <+> "::" <+> prettyGreenType t
prettyExpr (ListE xs) = list (map prettyExpr xs)
prettyExpr (TupleE xs) = tupled (map prettyExpr xs)

forallVars :: Type -> [Doc a]
forallVars (Forall (TV s) t) = pretty s : forallVars t
forallVars _ = []

forallBlock :: Type -> Doc a
forallBlock (Forall _ t) = forallBlock t
forallBlock t = prettyType t

prettyGreenType :: Type -> Doc AnsiStyle 
prettyGreenType t = annotate typeStyle (prettyType t)

prettyType :: Type -> Doc ann
prettyType UniT = "1"
prettyType (VarT (TV s)) = pretty s
prettyType (FunT t1@(FunT _ _) t2) = parens (prettyType t1) <+> "->" <+> prettyType t2
prettyType (FunT t1 t2) = prettyType t1 <+> "->" <+> prettyType t2
prettyType t@(Forall _ _) = "forall" <+> hsep (forallVars t) <+> "." <+> forallBlock t
prettyType (ExistT (TV e)) = "<" <> pretty e <> ">"
prettyType (ArrT (TV v) ts) = pretty v <+> hsep (map prettyType ts)

class Describable a where
  desc :: a -> String

instance Describable Expr where
  desc (UniE) = "UniE"
  desc (VarE (EV v)) = "VarE:" ++ T.unpack v
  desc (ListE _) = "ListE"
  desc (TupleE _) = "Tuple"
  desc (LamE (EV v) _) = "LamE:" ++ T.unpack v
  desc (AppE e1 e2) = "AppE (" ++ desc e1 ++ ") (" ++ desc e2 ++ ")"
  desc (AnnE e _) = "AnnE (" ++ desc e ++ ")"
  desc (IntE x) = "IntE:" ++ show x
  desc (NumE x) = "NumE:" ++ show x
  desc (LogE x) = "LogE:" ++ show x
  desc (StrE x) = "StrE:" ++ show x
  desc (Declaration (EV e) _) = "Declaration:" ++ T.unpack e
  desc (Signature (EV e) _) = "Signature:" ++ T.unpack e

instance Describable Type where
  desc (UniT) = "UniT"
  desc (VarT (TV v)) = "VarT:" ++ T.unpack v
  desc (ExistT (TV v)) = "ExistT:" ++ T.unpack v
  desc (Forall (TV v) _) = "Forall:" ++ T.unpack v
  desc (FunT t1 t2) = "FunT (" ++ desc t1 ++ ") (" ++ desc t2 ++ ")"
  desc (ArrT (TV v) xs) = "ArrT:" ++ T.unpack v ++ " " ++ (concat . map desc) xs
