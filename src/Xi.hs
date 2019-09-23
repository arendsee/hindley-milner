{-|
Module      : Xi
Description : The primary API for Xi
Copyright   : (c) Zebulun Arendsee, 2019
License     : GPL-3
Maintainer  : zbwrnz@gmail.com
Stability   : experimental
-}

module Xi (
    parse
  , typecheck
  , cute
  , ugly
  , ignoreSource
  , localModules
  , XP.readType
  , Module(..)
  , MVar(..)
  , EVar(..)
  , TVar(..)
  , Expr(..)
  , EType(..)
  , Type(..)
  , Property(..)
  , Constraint(..)
  , TypeError(..)
  , TypeSet(..)
  , Filename
  , Language
) where

import Xi.Data
import Xi.Util
import qualified Xi.Infer as XI 
import qualified Xi.Parser as XP
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Control.Monad as CM
import qualified Data.Text.IO as DIO
import qualified System.FilePath.Posix as SFP
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

parse
  :: (Filename -> IO ()) -- ^ check existence of a source (file, URL, or whatever)
  -> (MVar -> IO (Maybe Filename, T.Text)) -- ^ open a module (file, URL, or whatever)
  -> Maybe Filename
  -> T.Text -- ^ code of the current module
  -> IO [Module]
parse checkSource loadModule f code = fmap Map.elems $ parse' Map.empty (f, code) where
  parse' :: (Map.Map MVar Module) -> (Maybe Filename, T.Text) -> IO (Map.Map MVar Module)
  parse' visited (f', code') = CM.foldM parse'' visited (XP.readProgram f' code')

  parse'' :: (Map.Map MVar Module) -> Module -> IO (Map.Map MVar Module)
  parse'' visited m
    | Map.member (moduleName m) visited = return visited
    | otherwise = do
        checkSources checkSource m
        imports <- mapM loadModule [n | (n, _, _) <- moduleImports m]
        CM.foldM parse' (Map.insert (moduleName m) m visited) imports

-- assert that all sourced resources exist
checkSources :: (Filename -> IO ()) -> Module -> IO ()
checkSources f m = chk' (moduleBody m) where
  chk' ((SrcE _ (Just filename) _):es) = f filename >> chk' es
  chk' (_:es) = chk' es
  chk' [] = return ()

typecheck
  :: [Module]
  -> Either TypeError [Module]
typecheck ms =
  case runStack (XI.typecheck ms) of
    (Right result, _) -> Right result
    (Left err, _) -> Left err

cute :: Either TypeError [Module] -> IO ()
cute (Right es) = mapM_ (\e -> putDoc (prettyModule e) >> putStrLn "") es
cute (Left err) = print err

ugly :: Either TypeError [Module] -> IO ()
ugly (Right es) = print es
ugly (Left err) = print err

-- do not check existence of source files
ignoreSource :: T.Text -> IO () 
ignoreSource _ = return ()

localModules :: Maybe String -> MVar -> IO (Maybe Filename, T.Text)
localModules (Just filename) (MV f) = do
  code <- DIO.readFile . SFP.replaceFileName filename $ (T.unpack f <> ".loc")
  return (Just (T.pack filename), code)
localModules Nothing (MV f) = do
  let filename = T.unpack f <> ".loc"
  code <- DIO.readFile filename
  return (Just . T.pack $ filename, code)
