module Xi (parse, typecheck, cute, ugly) where

import Xi.Data
import qualified Xi.Infer as XI 
import qualified Xi.Parser as XP
import qualified Data.Text as T
import qualified Data.Map as Map
import qualified Safe as Safe
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
  parse'' visited mod
    | Map.member (moduleName mod) visited = return visited
    | otherwise = do
        checkSources checkSource mod
        imports <- mapM loadModule [m | (m, _, _) <- moduleImports mod]
        CM.foldM parse' (Map.insert (moduleName mod) mod visited) imports

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
