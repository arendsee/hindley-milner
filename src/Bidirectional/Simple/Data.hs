module Bidirectional.Simple.Data
(
    Infer
  , throw
  , Expr(..)
  , VarE(..)
  , VarT(..)
  , Type(..)
  , Gamma(..)
  , TypeError(..)
) where

import qualified Data.Map as Map
import Data.Text.Prettyprint.Doc

newtype VarE = VE String deriving(Show, Ord, Eq)
newtype VarT = VT String deriving(Show, Ord, Eq)

newtype Gamma = Gamma (Map.Map VarE Type) 

type Infer = Either TypeError Type

throw :: TypeError -> Infer 
throw err = Left err

data TypeError
  = BadThingHappened Expr
  | CallingNonfunction Expr
  | IfelseBlockTypeMismatch Expr
  | NeedExplicitTypeSignature Expr
  | UnboundVariable String
  | TypeMismatch Expr Type Type
  | ListTypeMismatch Expr Type
  | BadLiterature Expr
  | BadList Expr
  | EmptyList
  deriving(Show, Ord, Eq)

data Expr
  = Var VarE 
  | App Expr Expr
  | Lam VarE Expr
  | If Expr Expr Expr
  | Ann Expr Type -- ^ A type annotation
  | Num Integer
  | Log Bool
  | Lst [Expr]
  deriving(Show, Ord, Eq)

-- | Strictly speaking TLst, TLog and TNum are not necessary, but using them
-- makes the Infer code tidier. These types can be considered "builtins" since
-- Expr has special syntax for them.
data Type
  = NilT
  | ArrT VarT [Type] -- ^ t1 [t2]
  | LamT Type Type -- ^ t1 -> t2
  | LstT Type -- ^ Same as @TArr (TV "List") [a]@
  | LogT -- ^ Same as @TArr (TV "Bool") []@
  | NumT -- ^ Same as @TArr (TV "Num") []@
  deriving(Show, Ord, Eq)



instance Pretty VarE where
  pretty (VE n) = pretty n

instance Pretty VarT where
  pretty (VT n) = pretty n

instance Pretty TypeError where
  pretty (BadThingHappened e) = "BadThingHappened:" <+> pretty e
  pretty (CallingNonfunction e) = "CallingNonfunction:" <+> pretty e
  pretty (IfelseBlockTypeMismatch e) = "IfelseBlockTypeMismatch:" <+> pretty e
  pretty (NeedExplicitTypeSignature e) = "NeedExplicitTypeSignature:" <+> pretty e
  pretty (UnboundVariable s) = "UnboundVariable:" <+> pretty s
  pretty (TypeMismatch e t1 t2)
    = "TypeMismatch in" <+> pretty e <> line 
    <> "  Expected:" <+> pretty t1 <> line
    <> "  Actual:" <+> pretty t2
  pretty (BadLiterature e) = "BadLiterature:" <+> pretty e
  pretty (BadList l) = "Heterogenous lists are not supported:" <+> pretty l
  pretty EmptyList = "Cannot infer type of empty list without an explicit type signature"
  pretty (ListTypeMismatch e t)
    =   "Expected the list '" <> pretty e <> "'"
    <+> "to have a list type, but found '" <> pretty t <> "'"

instance Pretty Type where
  pretty NilT = "()"
  pretty (LamT t1@(LamT _ _) t2) = parens (pretty t1) <+> "->" <+> pretty t2
  pretty (LamT t1 t2) = pretty t1 <+> "->" <+> pretty t2
  pretty (ArrT t1 []) = pretty t1
  pretty (ArrT t1 ts) = pretty t1 <+> hsep (map pretty' ts) where
    pretty' (ArrT t []) = pretty t
    pretty' t = parens (pretty t)
  pretty (LstT t) = brackets (pretty t)
  pretty LogT = "Bool"
  pretty NumT = "Num"

instance Pretty Expr where
  pretty (Var (VE n)) = pretty n
  pretty (App e1@(Var _) e2@(Var _)) = pretty e1 <+> pretty e2
  pretty (App e1@(Var _) e2) = pretty e1 <+> parens (pretty e2)
  pretty (App e1 e2@(Var _)) = pretty e1 <+> pretty e2
  pretty (App e1 e2) = parens (pretty e1) <+> parens (pretty e2)
  pretty (Lam (VE n) e) = "\\" <+> pretty n <+> "->" <+> pretty e
  pretty (If cond e1 e2)
    =  "if" <+> pretty cond <> line
    <> "then" <+> pretty e1 <> line
    <> "else" <+> pretty e2
  pretty (Ann e@(Var _) t) = pretty e <+> "::" <+> pretty t
  pretty (Ann e@(Log _) t) = pretty e <+> "::" <+> pretty t
  pretty (Ann e@(Num _) t) = pretty e <+> "::" <+> pretty t
  pretty (Ann e t) = parens (pretty e) <+> "::" <+> pretty t
  pretty (Log True) = "true"
  pretty (Log False) = "false"
  pretty (Num i) = pretty i
  pretty (Lst xs) = list (map pretty xs)
