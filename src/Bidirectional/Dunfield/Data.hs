module Bidirectional.Dunfield.Data
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
  , accessWith
  , accessWith2
  , lookupT
  , lookupE
  , throwError
  , runStack
  , index
  -- * State manipulation
  , depth
  , incDepth
  , decDepth
  , newvar
  -- * Pretty printing
  , Doc'
  -- * Config handling
  , verbosity
) where

import qualified Data.List as DL
import Control.Monad.Except (throwError)
import qualified Control.Monad.Except as ME
import qualified Control.Monad.State as MS
import qualified Control.Monad.Writer as MW
import qualified Control.Monad.Reader as MR
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Render.Terminal.Internal

type Doc' = Doc AnsiStyle

type GeneralStack c e l s a = MR.ReaderT c (ME.ExceptT e (MW.WriterT l (MS.StateT s IO))) a
type Stack a = GeneralStack StackConfig TypeError [String] StackState a

-- | currently I do nothing with the Reader and Writer monads, but I'm leaving
-- them in for now since I will need them when I plug this all into Morloc.
runStack :: Stack a -> Int -> IO (Either TypeError a)
runStack e verbosity = do
  ((e, _), _) <- MS.runStateT(MW.runWriterT(ME.runExceptT(MR.runReaderT e (StackConfig verbosity)))) emptyState
  return e

type Gamma = [GammaIndex]
newtype EVar = EV String deriving(Show, Eq, Ord)
newtype TVar = TV String deriving(Show, Eq, Ord)

data StackState = StackState {
      stateVar :: Int
    , stateDepth :: Int
  } deriving(Ord, Eq, Show)
emptyState = StackState 0 0

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
  | IntE Integer | NumE Double | LogE Bool | StrE String
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

data Monotype
  = UniM
  | VarM TVar
  | ExistM TVar
  | FunM Monotype Monotype
  deriving(Show, Ord, Eq)

data TypeError
  = UnknownError
  | SubtypeError
  | ExistentialError
  | BadExistentialCast
  | AccessError
  | NonFunctionDerive
  | UnboundVariable
  | OccursCheckFail
  | EmptyCut
  | TypeMismatch
  | UnexpectedPattern Expr Type
  | ToplevelRedefinition
  | UnkindJackass
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

accessWith :: (Indexable a) => (GammaIndex -> GammaIndex) -> a -> Gamma -> Stack Gamma
accessWith f gi gs = case access1 gi gs of
  (Just (ls, x, rs)) -> return $ ls <> (f x:rs)
  Nothing -> throwError AccessError

accessWith2
  :: (Indexable a)
  => (GammaIndex -> GammaIndex) -> (GammaIndex -> GammaIndex)
  -> a -> a -> Gamma -> Stack Gamma
accessWith2 f g lgi rgi gs = case access2 lgi rgi gs of
  (Just (ls, x, ms, y, rs)) -> return $ ls <> (f x:ms) <> (g y:rs)
  Nothing -> throwError AccessError

newvar :: Stack Type
newvar = do
  s <- MS.get 
  let v = newvars !! stateVar s
  MS.put $ s {stateVar = stateVar s + 1}
  return (ExistT $ TV v)
  where
    newvars = zipWith (\x y -> x ++ show y) (repeat "t") ([0..] :: [Integer])

incDepth :: Stack ()
incDepth = do
  s <- MS.get
  MS.put $ s {stateDepth = stateDepth s + 1 } 

decDepth :: Stack ()
decDepth = do
  s <- MS.get
  MS.put $ s {stateDepth = stateDepth s - 1 } 

depth :: Stack Int
depth = MS.gets stateDepth

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


instance Pretty EVar where
  pretty (EV n) = pretty n

instance Pretty TVar where
  pretty (TV n) = pretty n

instance Pretty TypeError where
  pretty UnknownError            = "UnknownError: ???"
  pretty SubtypeError            = "SubtypeError: ???"
  pretty ExistentialError        = "ExistentialError: probably a bug"
  pretty BadExistentialCast      = "BadExistentialCast"
  pretty AccessError             = "Bad access attempt"
  pretty NonFunctionDerive       = "Derive should only be called on function applications"
  pretty UnboundVariable         = "Unbound variable"
  pretty OccursCheckFail         = "OccursCheckFail"
  pretty EmptyCut                = "EmptyCut - probably a logic bug"
  pretty TypeMismatch            = "TypeMismatch"
  pretty (UnexpectedPattern e t) = "UnexpectedPattern: " <> pretty e <> "|" <> pretty t
  pretty ToplevelRedefinition    = "ToplevelRedefinition"
  pretty UnkindJackass           = "UnkindJackass"

instance Pretty Type where
  pretty UniT = "1"
  pretty (VarT (TV s)) = pretty s
  pretty (FunT t1@(FunT _ _) t2) = parens (pretty t1) <+> "->" <+> pretty t2
  pretty (FunT t1 t2) = pretty t1 <+> "->" <+> pretty t2
  pretty t@(Forall (TV s) t') = "forall" <+> hsep (forallVars t) <+> "." <+> forallBlock t
  pretty (ExistT e) = "<" <> pretty e <> ">"
  pretty (ArrT v ts) = pretty v <+> hsep (map pretty ts)

forallVars :: Type -> [Doc a]
forallVars (Forall s t) = pretty s : forallVars t
forallVars _ = []

forallBlock :: Type -> Doc a
forallBlock (Forall s t) = forallBlock t
forallBlock t = pretty t

instance Pretty Expr where
  pretty UniE = "()"
  pretty (VarE (EV s)) = pretty s
  pretty (LamE (EV n) e) = "\\" <> pretty n <+> "->" <+> pretty e
  pretty (AnnE e t) = pretty e <+> ":" <+> pretty t
  pretty (AppE e1 e2) = parens (pretty e1) <+> pretty e2
  pretty (IntE x) = pretty x
  pretty (NumE x) = pretty x
  pretty (StrE x) = dquotes (pretty x)
  pretty (LogE x) = pretty x
  pretty (Declaration v e1 e2) = pretty v <+> "=" <+> pretty e1 <> ";" <+> pretty e2
  pretty (Signature v t e2) = pretty v <+> "::" <+> pretty t <> ";" <+> pretty e2
  pretty (ListE xs) = list (map pretty xs)

instance Pretty GammaIndex where 
  pretty (VarG t) = pretty t
  pretty (AnnG e t) = pretty (AnnE e t)
  pretty (ExistG t) = "<" <> pretty t <> ">"
  pretty (SolvedG v t) = "<" <> pretty v <> "> = " <> pretty t
  pretty (MarkG t) = "#" <> pretty t
