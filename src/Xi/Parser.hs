module Xi.Parser (readProgram, readType) where

import Xi.Data
import Text.Megaparsec
import Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import Data.Void (Void)

type Parser = Parsec Void T.Text

many1 :: Parser a -> Parser [a]
many1 p = do
  x <- p
  xs <- many p
  return (x:xs)

sc :: Parser ()
sc = L.space space1 empty empty

symbol = L.symbol sc

-- A lexer where space is consumed after every token (but not before)
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

integer :: Parser Integer
integer = lexeme $ L.signed sc L.decimal

number :: Parser Double
number = lexeme $ L.signed sc L.float

parens :: Parser a -> Parser a
parens p = lexeme $ between (symbol "(") (symbol ")") p

brackets :: Parser a -> Parser a
brackets p = lexeme $ between (symbol "[") (symbol "]") p

braces :: Parser a -> Parser a
braces p = lexeme $ between (symbol "{") (symbol "}") p

angles :: Parser a -> Parser a
angles p = lexeme $ between (symbol "<") (symbol ">") p

name :: Parser T.Text
name = lexeme $ do
  f <- C.letterChar
  rs <- many C.alphaNumChar
  return (T.pack $ f:rs)

readProgram :: T.Text -> [Module]
readProgram s = case parse (pProgram <* eof) "" s of 
      Left err -> error (show err)
      Right es -> es

data Toplevel
  = TModule Module
  | TModuleExpression ModuleExpression 

data ModuleExpression
  = Import [(MVar, EVar, Maybe EVar)]
  -- ^ module name, function name and optional alias
  | Export EVar
  | Expression Expr

pProgram :: Parser [Module]
pProgram = do
  es <- sepBy pToplevel (symbol ";")
  let mods = [m | (TModule m) <- es]
  case [e | (TModuleExpression e) <- es] of
    [] -> return mods
    es' -> return $ makeModule (MV "Main") es' : mods

pToplevel :: Parser Toplevel
pToplevel =   try (fmap TModule pModule)
          <|> fmap TModuleExpression pModuleExpression

pModule :: Parser Module
pModule = do
  _ <- symbol "module"
  moduleName <- name
  mes <- braces ( sepBy pModuleExpression (symbol ";") )
  return $ makeModule (MV moduleName) mes

makeModule :: MVar -> [ModuleExpression] -> Module
makeModule n mes = Module {
      moduleName = n
    , moduleImports = imports'
    , moduleExports = exports'
    , moduleExpressions = expressions'
  } where
  imports' = concat $ [x | (Import x) <- mes]
  exports' = [x | (Export x) <- mes]
  expressions' = [x | (Expression x) <- mes]

pModuleExpression :: Parser ModuleExpression
pModuleExpression
  =   try pImport
  <|> try pExport
  <|> try pStatement'
  <|> pExpr'
  where
    pStatement' = fmap Expression pStatement
    pExpr' = fmap Expression pExpr

pImport :: Parser ModuleExpression
pImport = do
  _ <- symbol "import"
  moduleName <- name
  functions <- parens (sepBy pImportTerm (symbol ","))
  return $ Import [(MV moduleName, e, a) | (e, a) <- functions]

pImportTerm :: Parser (EVar, Maybe EVar)
pImportTerm = do
  n <- name
  a <- optional (symbol "as" >> name)
  return (EV n, fmap EV a)

pExport :: Parser ModuleExpression
pExport = fmap (Export . EV) $ symbol "export" >> name

pStatement :: Parser Expr
pStatement = try pDeclaration <|> pSignature

pDeclaration :: Parser Expr
pDeclaration = try pFunctionDeclaration <|> pDataDeclaration
 
pDataDeclaration :: Parser Expr
pDataDeclaration = do
  v <- name
  _ <- symbol "="
  e <- pExpr
  return (Declaration (EV v) e)

pFunctionDeclaration :: Parser Expr
pFunctionDeclaration = do
  v <- name
  args <- many1 name
  _ <- symbol "="
  e <- pExpr
  return $ Declaration (EV v) (curryLamE (map EV args) e)
  where
    curryLamE [] e' = e'
    curryLamE (v:vs') e' = LamE v (curryLamE vs' e') 

pSignature :: Parser Expr
pSignature = do
  v <- name
  _ <- symbol "::"
  t <- pType
  return (Signature (EV v) t)

readType :: T.Text -> Type
readType s = case parse (pType <* eof) "" s of 
  Left err -> error (show err)
  Right t -> t 

pExpr :: Parser Expr
pExpr
  =   try pTuple
  <|> try pUni
  <|> try pAnn
  <|> try pApp
  <|> try pStrE
  <|> try pLogE
  <|> try pNumE
  <|> try pIntE
  <|> pListE
  <|> parens pExpr
  <|> pLam
  <|> pVar

pListE :: Parser Expr
pListE = fmap ListE $ brackets (sepBy pExpr (symbol ","))

pTuple :: Parser Expr
pTuple = do
  _ <- symbol "("
  e <- pExpr
  _ <- symbol ","
  es <- sepBy1 pExpr (symbol ",")
  _ <- symbol ")"
  return (TupleE (e:es))

pUni :: Parser Expr
pUni = symbol "UNIT" >> return UniE

pAnn :: Parser Expr
pAnn = do
  e <- parens pExpr <|> pVar <|> pListE <|> try pNumE <|> pIntE <|> pLogE <|> pStrE
  _ <- symbol "::"
  t <- pType
  return $ AnnE e t

pApp :: Parser Expr
pApp = do
  f <- parens pExpr <|> pVar
  (e:es) <- many1 s
  return $ foldl AppE (AppE f e) es
  where
    s =   try pAnn
      <|> try (parens pExpr)
      <|> try pUni
      <|> try pStrE
      <|> try pLogE
      <|> try pNumE
      <|> try pIntE
      <|> pListE
      <|> pVar

pIntE :: Parser Expr
pIntE = fmap IntE integer

pLogE :: Parser Expr
pLogE = pTrue <|> pFalse
  where
    pTrue = symbol "True" >> return (LogE True)
    pFalse = symbol "False" >> return (LogE False)

pStrE :: Parser Expr
pStrE = do
  _ <- symbol "\""
  s <- many (noneOf ['"'])
  _ <- symbol "\""
  return (StrE (T.pack s))

pNumE :: Parser Expr
pNumE = fmap NumE number

pLam :: Parser Expr
pLam = do
  _ <- symbol "\\"
  vs <- many1 pEVar
  _ <- symbol "->"
  e <- pExpr
  return (curryLamE vs e)
  where
    curryLamE [] e' = e'
    curryLamE (v:vs') e' = LamE v (curryLamE vs' e') 

pVar :: Parser Expr
pVar = fmap VarE pEVar

pEVar :: Parser EVar
pEVar = fmap EV name

pType :: Parser Type
pType
  =   pExistential
  <|> try pForAllT
  <|> try pArrT
  <|> try pFunT
  <|> pListT
  <|> parens pType
  <|> pVarT

pExistential :: Parser Type
pExistential = do
  v <- angles name
  return (ExistT (TV v))

pArrT :: Parser Type
pArrT = do
  v <- name
  args <- many1 pType'
  return $ ArrT (TV v) args
  where
    pType' = parens pType <|> pVarT <|> pListT

pFunT :: Parser Type
pFunT = do
  t <- pType'
  _ <- symbol "->"
  ts <- sepBy1 pType' (symbol "->")
  return $ foldr1 FunT (t:ts)
  where
    pType' = parens pType <|> try pArrT <|> pVarT <|> pListT

pListT :: Parser Type
pListT = fmap (\x -> ArrT (TV "List") [x]) (brackets pType)

pVarT :: Parser Type
pVarT = fmap (VarT . TV) name

pForAllT :: Parser Type
pForAllT = do
  _ <- symbol "forall"
  vs <- many1 name
  _ <- symbol "."
  t <- pType
  return (curryForall vs t)
  where
    curryForall [] e' = e'
    curryForall (v:vs') e' =  Forall (TV v) (curryForall vs' e') 
