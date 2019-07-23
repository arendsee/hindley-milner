module Bidirectional.Simple.Pretty ( pretty ) where

import Bidirectional.Simple.Data

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Render.Terminal.Internal

instance Pretty EVar where
  pretty (EV n) = pretty n

instance Pretty TypeError where
  pretty (BadThingHappened e) = "BadThingHappened:" <+> pretty e
  pretty (CallingNonfunction e) = "CallingNonfunction:" <+> pretty e
  pretty (IfelseBlockTypeMismatch e) = "IfelseBlockTypeMismatch:" <+> pretty e
  pretty (NeedExplicitTypeSignature e) = "NeedExplicitTypeSignature:" <+> pretty e
  pretty (UnboundVariable s) = "UnboundVariable:" <+> pretty s
  pretty (TypeMismatch e t1 t2)
    = "TypeMismatch in" <+> pretty e <> line 
    <> "Expected:" <+> pretty t1
    <> "Actual:" <+> pretty t2
  pretty (BadLiterature e) = "BadLiterature:" <+> pretty e

instance Pretty Type where
  pretty TBool = "Bool"
  pretty TEmpty = "()"
  pretty (TLam t1@(TLam _ _) t2) = parens (pretty t1) <+> "->" <+> pretty t2
  pretty (TLam t1 t2) = pretty t1 <+> "->" <+> pretty t2

instance Pretty Expr where
  pretty (Var (EV n)) = pretty n
  pretty (App e1@(Var _) e2@(Var _)) = pretty e1 <+> pretty e2
  pretty (App e1@(Var _) e2) = pretty e1 <+> parens (pretty e2)
  pretty (App e1 e2@(Var x)) = pretty e1 <+> pretty e2
  pretty (App e1 e2) = parens (pretty e1) <+> parens (pretty e2)
  pretty (Lam (EV n) e) = "\\" <+> pretty n <+> "->" <+> pretty e
  pretty (Lit True) = "true"
  pretty (Lit False) = "false"
  pretty (If cond e1 e2)
    =  "if" <+> pretty cond <> line
    <> "then" <+> pretty e1 <> line
    <> "else" <+> pretty e2
  pretty (Ann e@(Lit _) t) = pretty e <+> "::" <+> pretty t
  pretty (Ann e@(Var _) t) = pretty e <+> "::" <+> pretty t
  pretty (Ann e t) = parens (pretty e) <+> "::" <+> pretty t

typeStyle = SetAnsiStyle {
      ansiForeground  = Just (Vivid, Green) -- ^ Set the foreground color, or keep the old one.
    , ansiBackground  = Nothing             -- ^ Set the background color, or keep the old one.
    , ansiBold        = Nothing             -- ^ Switch on boldness, or don’t do anything.
    , ansiItalics     = Nothing             -- ^ Switch on italics, or don’t do anything.
    , ansiUnderlining = Just Underlined     -- ^ Switch on underlining, or don’t do anything.
  } 

prettyType :: Pretty a => a -> Doc AnsiStyle 
prettyType x = annotate typeStyle (pretty x)

cast :: Type -> Doc AnsiStyle -> Doc AnsiStyle
cast t d = d <> ":" <> prettyType t

pcast :: Type -> Doc AnsiStyle -> Doc AnsiStyle
pcast t d = parens d <> ":" <> prettyType t
