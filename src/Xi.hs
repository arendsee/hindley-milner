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
  , XP.readType
  , Module(..)
  , MVar(..)
  , EVar(..)
  , Expr(..)
  , EType(..)
  , Type(..)
  , Language(..)
  , Property(..)
  , Constraint(..)
  , TypeError(..)
  , Filename
) where

import Xi.Data
import qualified Xi.Infer as XI 
import qualified Xi.Parser as XP
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Control.Monad as CM
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

parse
  :: (Filename -> IO ()) -- ^ check existence of a source (file, URL, or whatever)
  -> (MVar -> IO T.Text) -- ^ open a module (file, URL, or whatever)
  -> T.Text -- ^ code of the current module
  -> IO [Module]
parse checkSource loadModule code = fmap Map.elems $ parse' Map.empty code where
  parse' :: (Map.Map MVar Module) -> T.Text -> IO (Map.Map MVar Module)
  parse' visited code' = CM.foldM parse'' visited (XP.readProgram code')

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
