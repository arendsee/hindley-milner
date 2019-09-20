module Xi (cute, ugly) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import qualified Data.Text as DT
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

run :: DT.Text -> Either TypeError [Module]
run expr = do
  case runStack (typecheck (readProgram expr)) of
    (Right result, _) -> Right result
    (Left err, _) -> Left err

cute :: DT.Text -> IO ()
cute expr = case run expr of
    (Right es) -> mapM_ (\e -> putDoc (prettyModule e) >> putStrLn "") es
    (Left err) -> print err

ugly :: DT.Text -> IO ()
ugly expr = case run expr of
    (Right es) -> print es
    (Left err) -> print err
