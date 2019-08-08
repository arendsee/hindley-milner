module Bidirectional.Dunfield.Parser (readExpr) where

import Bidirectional.Dunfield.Data
import Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.Parsec.Language as L

lexer = T.makeTokenParser (L.emptyDef {
      T.reservedNames = ["forall", "UNIT", "True", "False"]
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
  <|> try pAnn
  <|> try pApp
  <|> try pStrE
  <|> try pLogE
  <|> try pNumE
  <|> try pIntE
  <|> parens pExpr
  <|> pLam
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
  e2 <- parens pExpr
     <|> try pStrE <|> try pLogE <|> try pNumE <|> try pIntE
     <|> try pUni <|> pVar
  return (AppE e1 e2)

pIntE :: Parser Expr
pIntE = fmap IntE integer

pLogE :: Parser Expr
pLogE = pTrue <|> pFalse
  where
    pTrue = keyword "True" >> return (LogE True)
    pFalse = keyword "False" >> return (LogE False)

pStrE :: Parser Expr
pStrE = do
  _ <- char '"'
  s <- many (noneOf ['"'])
  _ <- char '"'
  return (StrE s)

pNumE :: Parser Expr
pNumE = do
  s <- option "" (string "-")
  w <- many digit
  _ <- char '.'
  d <- many1 digit
  let numStr = s ++ w ++ "." ++ d
  return $ NumE (read numStr :: Double)

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
  <|> try pForAllT
  <|> pVarT

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
