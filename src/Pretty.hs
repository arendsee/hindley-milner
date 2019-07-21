module Pretty (
  prettyTerm
) where

import Infer 

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text.Prettyprint.Doc.Render.Terminal.Internal

instance Pretty TVar where
  pretty (TV n) = pretty n

instance Pretty EVar where
  pretty (EV n) = pretty n

instance Pretty Type where
  pretty (TVar n) = pretty n
  pretty (TArr t1@(TArr _ _) t2) = parens (pretty t1) <+> "->" <+> pretty t2
  pretty (TArr t1 t2) = pretty t1 <+> "->" <+> pretty t2
  pretty (TLit l) = pretty l

instance Pretty TLiteral where
  pretty TInt = "Int"
  pretty TBool = "Bool"

instance Pretty (Expr a) where
  pretty (Var (EV n) _) = pretty n
  pretty (App e1@(Var _ _) e2@(Var _ _) _) = pretty e1 <+> pretty e2
  pretty (App e1@(Var _ _) e2 _) = pretty e1 <+> parens (pretty e2)
  pretty (App e1 e2@(Var x _) _) = pretty e1 <+> pretty e2
  pretty (App e1 e2 _) = parens (pretty e1) <+> parens (pretty e2)
  pretty (Lam (EV n) _ e _) = "\\" <+> pretty n <+> "->" <+> pretty e
  pretty (Let (EV n) _ e1 e2 _) =
       nest 4 (vsep ["let" <+> pretty n <+> "=", pretty e1]) <> line
    <> nest 4 (vsep ["in", pretty e2])
  pretty (Lit (PInt i) _) = pretty i
  pretty (Lit (PBool b) _) = pretty b


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

prettyTerm :: Expr Type -> Doc AnsiStyle
prettyTerm (Var (EV n) t) = cast t $ pretty n
prettyTerm (App e1@(Var _ _) e2@(Var _ _) t) = pcast t $ prettyTerm e1 <+> prettyTerm e2
prettyTerm (App e1@(Var _ _) e2 t) = pcast t $ prettyTerm e1 <+> parens (prettyTerm e2)
prettyTerm (App e1 e2@(Var x _) t) = pcast t $ prettyTerm e1 <+> prettyTerm e2
prettyTerm (App e1 e2 t) = pcast t $ parens (prettyTerm e1) <+> parens (prettyTerm e2)
prettyTerm (Lam (EV n) t1 e t2) = pcast t2 $ "\\" <+> cast t1 (pretty n) <+> "->" <+> prettyTerm e
prettyTerm (Let (EV n) _ e1 e2 t)
  =  "_ ::" <+> prettyType t <> line
  <> nest 4 (vsep ["let" <+> pretty n <+> "=", prettyTerm e1]) <> line
  <> nest 4 (vsep ["in", prettyTerm e2])
prettyTerm (Lit (PInt i) _) = pretty i
prettyTerm (Lit (PBool b) _) = pretty b
