module Xi.Parser (readProgram, readType) where

import Xi.Data
import Text.Megaparsec
import Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Text as T
import Data.Void (Void)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Scientific as DS

type Parser = Parsec Void T.Text

readProgram :: T.Text -> [Module]
readProgram s = case parse (sc >> pProgram <* eof) "" s of 
      Left err -> error (show err)
      Right es -> es

many1 :: Parser a -> Parser [a]
many1 p = do
  x <- p
  xs <- many p
  return (x:xs)

-- sc stands for space consumer
sc :: Parser ()
sc = L.space space1 lineComment blockComment
  where
    lineComment  = L.skipLineComment "--"
    blockComment = L.skipBlockComment "{-" "-}"

symbol = L.symbol sc

-- A lexer where space is consumed after every token (but not before)
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

number :: Parser DS.Scientific
number = lexeme $ L.signed sc L.scientific -- `empty` because no space is allowed

parens :: Parser a -> Parser a
parens p = lexeme $ between (symbol "(") (symbol ")") p

brackets :: Parser a -> Parser a
brackets p = lexeme $ between (symbol "[") (symbol "]") p

braces :: Parser a -> Parser a
braces p = lexeme $ between (symbol "{") (symbol "}") p

angles :: Parser a -> Parser a
angles p = lexeme $ between (symbol "<") (symbol ">") p

reservedWords :: [T.Text]
reservedWords = ["module", "source", "from", "where", "import",
                 "export", "as", "True", "False"]

operatorChars :: String
operatorChars = ":!$%&*+./<=>?@\\^|-~#"

op :: T.Text -> Parser T.Text
op o = (lexeme . try) (symbol o <* notFollowedBy (oneOf operatorChars))

reserved :: T.Text -> Parser T.Text
reserved w = try (symbol w)

stringLiteral :: Parser T.Text
stringLiteral = do
  _ <- symbol "\""
  s <- many (noneOf ['"'])
  _ <- symbol "\""
  return $ T.pack s

name :: Parser T.Text
name = (lexeme . try) (p >>= check) where
  p       = fmap T.pack $ (:) <$> letterChar <*> many (alphaNumChar <|> char '_')
  check x = if elem x reservedWords
              then failure Nothing Set.empty -- TODO: error message
              else return x

data Toplevel
  = TModule Module
  | TModuleBody ModuleBody 

data ModuleBody
  = Import [(MVar, EVar, Maybe EVar)]
  -- ^ module name, function name and optional alias
  | Export EVar
  | Body Expr

pProgram :: Parser [Module]
pProgram = do
  es <- many pToplevel
  let mods = [m | (TModule m) <- es]
  case [e | (TModuleBody e) <- es] of
    [] -> return mods
    es' -> return $ makeModule (MV "Main") es' : mods

pToplevel :: Parser Toplevel
pToplevel =   try (fmap TModule pModule <* optional (symbol ";"))
          <|> fmap TModuleBody (pModuleBody <* optional (symbol ";"))

pModule :: Parser Module
pModule = do
  _ <- reserved "module"
  moduleName <- name
  mes <- braces ( many1 pModuleBody)
  return $ makeModule (MV moduleName) mes

makeModule :: MVar -> [ModuleBody] -> Module
makeModule n mes = Module {
      moduleName = n
    , moduleImports = imports'
    , moduleExports = exports'
    , moduleBody = body'
  } where
  imports' = concat $ [x | (Import x) <- mes]
  exports' = [x | (Export x) <- mes]
  body' = [x | (Body x) <- mes]

pModuleBody :: Parser ModuleBody
pModuleBody
  =   try pImport <* optional (symbol ";")
  <|> try pExport <* optional (symbol ";")
  <|> try pStatement' <* optional (symbol ";")
  <|> pExpr' <* optional (symbol ";")
  where
    pStatement' = fmap Body pStatement
    pExpr' = fmap Body pExpr

pImport :: Parser ModuleBody
pImport = do
  _ <- reserved "import"
  n <- name
  functions <-   parens (sepBy pImportTerm (symbol ","))
            <|>  fmap (\x -> [(EV x, Nothing)]) name
  return $ Import [(MV n, e, a) | (e, a) <- functions]

pImportTerm :: Parser (EVar, Maybe EVar)
pImportTerm = do
  n <- name
  a <- optional (reserved "as" >> name)
  return (EV n, fmap EV a)

pExport :: Parser ModuleBody
pExport = fmap (Export . EV) $ reserved "export" >> name

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
  lang <- optional (name)
  _ <- symbol "::"
  props <- option [] (try $ sepBy1 pProperty (symbol ",") <* symbol "=>")
  t <- pType
  constraints <- option [] $ reserved "where" >> parens (sepBy1 pConstraint (symbol ","))
  return $ Signature (EV v) (EType
    { etype = t
    , elang = fmap Lang lang
    , eprop = Set.fromList props
    , econs = Set.fromList constraints
    , esource = Nothing
    })

-- | match an optional tag that precedes some construction
tag :: Parser a -> Parser (Maybe T.Text)
tag p =
  optional (try tag')
  where
    tag' = do
      l <- name
      _ <- op ":"
      _ <- lookAhead p
      return l

pProperty :: Parser Property
pProperty = do 
  ps <- many1 name
  case ps of
    ["pack"] -> return Pack
    ["unpack"] -> return Unpack
    ["cast"] -> return Cast
    _ -> return (GeneralProperty ps)

pConstraint :: Parser Constraint
pConstraint = fmap (Con . T.pack) (many1 (noneOf [',']))

readType :: T.Text -> Type
readType s = case parse (pType <* eof) "" s of 
  Left err -> error (show err)
  Right t -> t 

pExpr :: Parser Expr
pExpr
  =   try pRecordE
  <|> try pTuple
  <|> try pUni
  <|> try pAnn
  <|> try pApp
  <|> try pStrE
  <|> try pLogE
  <|> try pNumE
  <|> try pSrcE
  <|> pListE
  <|> parens pExpr
  <|> pLam
  <|> pVar

-- source "c" from "foo.c" ("Foo" as foo, "bar")
-- source "R" ("sqrt", "t.test" as t_test)
pSrcE :: Parser Expr
pSrcE = do
  reserved "source"
  language <- stringLiteral 
  srcfile <- optional (reserved "from" >> stringLiteral)
  rs <- parens (sepBy1 pImportSourceTerm (symbol ","))
  return $ SrcE (Lang language) srcfile rs

pImportSourceTerm :: Parser (EVar, Maybe EVar)
pImportSourceTerm = do
  n <- stringLiteral
  a <- optional (reserved "as" >> name)
  return (EV n, fmap EV a)

pRecordE :: Parser Expr
pRecordE = fmap RecE $ braces (sepBy1 pRecordEntryE (symbol ","))

pRecordEntryE :: Parser (EVar, Expr)
pRecordEntryE = do
  n <- name
  _ <- symbol "="
  e <- pExpr
  return (EV n, e)

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
  e <- parens pExpr <|> pVar <|> pListE <|> try pNumE <|> pLogE <|> pStrE
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
      <|> pListE
      <|> pVar

pLogE :: Parser Expr
pLogE = pTrue <|> pFalse
  where
    pTrue = reserved "True" >> return (LogE True)
    pFalse = reserved "False" >> return (LogE False)

pStrE :: Parser Expr
pStrE = fmap StrE stringLiteral

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
  <|> try pUniT
  <|> try pRecordT
  <|> try pForAllT
  <|> try pArrT
  <|> try pFunT
  <|> try (parens pType) -- tagged [ ]
  <|> pListT
  <|> pTupleT
  <|> pVarT

pUniT :: Parser Type
pUniT = do
  _ <- symbol "("
  _ <- symbol ")"
  return UniT

pTupleT :: Parser Type
pTupleT = do
  _ <- tag (symbol "(")
  ts <- parens (sepBy1 pType (symbol ","))
  let v = TV . T.pack $ "Tuple" ++ (show (length ts))
  return $ ArrT v ts

pRecordT :: Parser Type
pRecordT = do
  _ <- tag (symbol "{")
  record <- braces (sepBy1 pRecordEntryT (symbol ","))
  return $ RecT record

pRecordEntryT :: Parser (TVar, Type)
pRecordEntryT = do
  n <- name
  _ <- symbol "::"
  t <- pType
  return (TV n, t)

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
pListT = do
  label <- tag (symbol "[")
  t <- brackets pType
  return $ ArrT (TV "List") [t]

pVarT :: Parser Type
pVarT = do
  label <- tag (name <|> stringLiteral)
  n <- name <|> stringLiteral
  return $ VarT (TV n)

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
