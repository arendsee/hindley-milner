module Bidirectional.Simple.Parser (readExpr) where

import Bidirectional.Simple.Data
import Text.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T
import qualified Text.Parsec.Language as L

lexer = T.makeTokenParser (L.emptyDef {
      T.reservedNames = ["if", "then", "else", "true", "false", "Bool", "Num"]
    , T.reservedOpNames = ["::", "->", "\\", ","]
    , T.identStart = letter
    , T.identLetter = alphaNum <|> char '_'
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
  =   try pAnn
  <|> try pApp
  <|> parens pExpr
  <|> pIf
  <|> pLam
  <|> pVar
  <|> pNum
  <|> pLog
  <|> pLst

pAnn :: Parser Expr
pAnn = do
  e <- parens pExpr <|> pNum <|> pLog <|> pLst <|> pVar
  _ <- op "::"
  t <- pType
  return $ Ann e t

pApp :: Parser Expr
pApp = do
  e1 <- parens pExpr <|> pNum <|> pLog <|> pLst <|> pVar
  e2 <- parens pExpr <|> pNum <|> pLog <|> pLst <|> pVar
  return (App e1 e2)

pIf :: Parser Expr
pIf = do
  _ <- keyword "if"
  cond <- pExpr
  _ <- keyword "then"
  e1 <- pExpr
  _ <- keyword "else"
  e2 <- pExpr
  return (If cond e1 e2)

pLam :: Parser Expr
pLam = do
  _ <- op "\\"
  v <- pEVar
  _ <- op "->"
  e <- pExpr
  return (Lam v e)

pVar :: Parser Expr
pVar = fmap Var pEVar

pNum :: Parser Expr
pNum = fmap Num integer

pLog :: Parser Expr
pLog = pTrue <|> pFalse
  where
    pTrue = keyword "true" >> return (Log True)
    pFalse = keyword "false" >> return (Log False)

pLst :: Parser Expr
pLst = fmap Lst $ brackets (sepBy pExpr (op ","))

pEVar :: Parser VarE
pEVar = fmap VE name

pVarT :: Parser VarT
pVarT = fmap VT name

pType :: Parser Type
pType
  = try pFunT
  <|> parens pType
  <|> pLstT
  <|> pArrT
  <|> pNumT
  <|> pLogT

pNumT :: Parser Type
pNumT = keyword "Num" >> return NumT

pLogT :: Parser Type
pLogT = keyword "Bool" >> return LogT

pLstT :: Parser Type
pLstT = fmap LstT $ brackets pType

pFunT :: Parser Type
pFunT = do
  t <- p
  _ <- op "->"
  ts <- sepBy1 p (op "->")
  return $ foldr1 LamT (t:ts)
  where
    p = parens pFunT <|> pLstT <|> pLogT <|> pNumT <|> try pArrT

pArrT :: Parser Type
pArrT = do
  t <- pVarT
  ts <- many pType'
  return $ ArrT t ts
  where
    pType' = parens pType <|> pLstT <|> pLogT <|> pNumT <|> pArrTUn

pArrTUn :: Parser Type
pArrTUn = do
  t <- pVarT
  return $ ArrT t []
