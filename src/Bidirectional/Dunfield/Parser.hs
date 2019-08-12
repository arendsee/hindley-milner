module Bidirectional.Dunfield.Parser (readExpr) where

import Bidirectional.Dunfield.Data
import Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.Parsec.Language as L

lexer = T.makeTokenParser (L.emptyDef {
      T.reservedNames = ["forall", "UNIT", "True", "False"]
    , T.reservedOpNames = ["::", "->", "\\", ".", "=", ";"]
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
pExpr = try pStatement <|> pNonStatementExpr

pNonStatementExpr :: Parser Expr
pNonStatementExpr
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

pStatement :: Parser Expr
pStatement = try pDeclaration <|> pSignature
 
pDeclaration :: Parser Expr
pDeclaration = do
  v <- name
  _ <- op "="
  e1 <- pNonStatementExpr
  _ <- op ";"
  e2 <- pExpr
  return (Declaration (EV v) e1 e2)

pSignature :: Parser Expr
pSignature = do
  v <- name
  _ <- op "::"
  t <- pType
  _ <- op ";"
  e2 <- pExpr
  return (Signature (EV v) t e2)

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
  f <- parens pExpr <|> pVar
  es <- many1
     $   parens pExpr
     <|> try pStrE <|> try pLogE <|> try pNumE <|> try pIntE
     <|> try pUni <|> pVar
  return $ applyMany f es where
    applyMany f' [] = f' -- this shouldn't happen
    applyMany f' [e] = AppE f' e
    applyMany f' (e:es') = applyMany (AppE f' e) es'

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
  vs <- many1 pEVar
  _ <- op "->"
  e <- pExpr
  return (curry vs e)
  where
    curry [] e' = e'
    curry (v:vs') e' = LamE v (curry vs' e') 

pVar :: Parser Expr
pVar = fmap VarE pEVar

pEVar :: Parser EVar
pEVar = fmap EV name

pType :: Parser Type
pType
  =   try pArrT
  <|> try pFunT
  <|> parens pType
  <|> try pForAllT
  <|> pVarT

pArrT :: Parser Type
pArrT = do
  v <- name
  args <- many1 pType'
  return $ ArrT (TV v) args
  where
    pType' = parens pType <|> pVarT

pFunT :: Parser Type
pFunT = do
  t <- pType'
  _ <- op "->"
  ts <- sepBy1 pType' (op "->")
  return $ foldr1 FunT (t:ts)
  where
    pType' = parens pType <|> try pArrT <|> pVarT

pVarT :: Parser Type
pVarT = fmap (VarT . TV) name

pForAllT :: Parser Type
pForAllT = do
  _ <- keyword "forall"
  vs <- many1 name
  _ <- op "."
  t <- pType
  return (curry vs t)
  where
    curry [] e' = e'
    curry (v:vs') e' =  Forall (TV v) (curry vs' e') 
