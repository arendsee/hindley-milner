module Bidirectional.Dunfield.Parser (readExpr) where

import Bidirectional.Dunfield.Data
import Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.Parsec.Language as L

lexer = T.makeTokenParser (L.emptyDef {
      T.reservedNames = ["forall, UNIT"]
    , T.reservedOpNames = ["::", "->", "\\", "."]
    , T.identStart = letter
    , T.identLetter = alphaNum
  })

type Parser = Parsec String ()

parens = T.parens lexer
brackets = T.brackets lexer
name = T.identifier lexer
op = T.reservedOp lexer
keyword = T.reserved lexer
integer = T.integer lexer

readExpr :: String -> Expr
readExpr s = case parse (pExpr <* eof) "" s of 
  Left err -> error (show err)
  Right expr -> expr

pExpr :: Parser Expr
pExpr
  =   try pUni
  <|> parens pExpr
  <|> pLam
  <|> try pAnn
  <|> try pApp
  <|> pVar

pUni :: Parser Expr
pUni = keyword "UNIT" >> return UniE

pAnn :: Parser Expr
pAnn = do
  e <- parens pExpr <|> pVar
  _ <- op "::"
  t <- pType
  return $ AnnE e t

pApp :: Parser Expr
pApp = do
  e1 <- parens pExpr <|> pVar
  e2 <- parens pExpr <|> pVar
  return (AppE e1 e2)

pLam :: Parser Expr
pLam = do
  _ <- op "\\"
  v <- pEVar
  _ <- op "->"
  e <- pExpr
  return (LamE v e)

pVar :: Parser Expr
pVar = fmap VarE pEVar

pEVar :: Parser EVar
pEVar = fmap EV name

pType :: Parser Type
pType
  = try pFunT
  <|> parens pType
  <|> pVarT
  <|> pForAllT

pFunT :: Parser Type
pFunT = do
  t <- pType'
  _ <- op "->"
  ts <- sepBy1 pType' (op "->")
  return $ foldr1 FunT (t:ts)
  where
    pType' = parens pType <|> pVarT

pVarT :: Parser Type
pVarT = fmap (VarT . TV) name

pForAllT :: Parser Type
pForAllT = do
  _ <- keyword "forall"
  v <- name
  _ <- op "."
  t <- pType
  return $ Forall (TV v) t
