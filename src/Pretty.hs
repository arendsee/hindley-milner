module Pretty where

import TypedExpr
import Type
import Expr

class Pretty a where
  pretty :: a -> String

instance Pretty TypedExpr where
  pretty (EVar n t) = n ++ ":" ++ pretty t
  pretty (EApp e1 e2 t) = "(" ++ pretty e1 ++ " " ++ pretty e2 ++ "):" ++ pretty t
  pretty (EArr (Arg n _) e t) = "(\\" ++ n ++ " . " ++ pretty e ++ "):" ++ pretty t 
  pretty (ELet n e1 e2 t) = "(let " ++ n ++ " = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ":):" ++ pretty t

instance Pretty Type where
  pretty (TVar n) = n
  pretty t@(TArr t1 t2) = case fromFunction t of
    Just (a, b) -> "(" ++ pretty a ++ " -> " ++ pretty b ++ ")"
    Nothing -> "(" ++ pretty t1 ++ " " ++ pretty t2 ++ ")"
