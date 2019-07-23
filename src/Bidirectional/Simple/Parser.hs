module Bidirectional.Simple.Parser (readExpr) where

import Bidirectional.Simple.Data
import Text.Parsec
import Text.Parsec.Char
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.Parsec.Language as L

lexer = T.makeTokenParser (L.emptyDef {
      T.reservedNames = ["if", "then", "else", "true", "false", "Bool"]
    , T.reservedOpNames = ["::", "->", "\\"]
    , T.identStart = letter
    , T.identLetter = alphaNum <|> char '_'
  })

type Parser = Parsec String ()

parens = T.parens lexer
name = T.identifier lexer
op = T.reservedOp lexer
keyword = T.reserved lexer

readExpr :: String -> Expr
readExpr s = case parse (pExpr <* eof) "" s of 
  Left err -> error (show err)
  Right expr -> expr

pExpr :: Parser Expr
pExpr
  =   try pAnn
  <|> try pApp
  <|> parens pExpr
  <|> pIf
  <|> pLit
  <|> pLam
  <|> pVar

pAnn :: Parser Expr
pAnn = do
  e <- parens pExpr <|> pVar <|> pLit
  _ <- op "::"
  t <- pType
  return $ Ann e t

pVar :: Parser Expr
pVar = fmap Var pEVar

pApp :: Parser Expr
pApp = do
  e1 <- parens pExpr <|> pLit <|> pVar
  e2 <- parens pExpr <|> pLit <|> pVar
  return (App e1 e2)

pLam :: Parser Expr
pLam = do
  _ <- op "\\"
  v <- pEVar
  _ <- op "->"
  e <- pExpr
  return (Lam v e)

pLit :: Parser Expr
pLit = fmap Lit pBool

pIf :: Parser Expr
pIf = do
  _ <- keyword "if"
  cond <- pExpr
  _ <- keyword "then"
  e1 <- pExpr
  _ <- keyword "else"
  e2 <- pExpr
  return (If cond e1 e2)

pBool :: Parser Bool
pBool = pTrue <|> pFalse
  where
    pTrue = keyword "true" >> return True
    pFalse = keyword "false" >> return False

pEVar :: Parser EVar
pEVar = fmap EV name

pType :: Parser Type
pType
  = try pFunT
  <|> parens pType
  <|> pBoolT

pFunT :: Parser Type
pFunT = do
  ts <- sepBy1 (pBoolT <|> (parens pFunT)) (op "->")
  return (associate ts)
  where
    associate :: [Type] -> Type
    associate [] = TEmpty
    associate [t] = t
    associate (t:ts) = TLam t (associate ts)

pBoolT :: Parser Type
pBoolT = keyword "Bool" >> return TBool
