module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

typecheckText :: Int -> Text -> IO ()
typecheckText v expr = do
  case runStack (typecheck (readProgram expr)) v of
    (Right es, _) -> mapM_ (\e -> putDoc (prettyExpr e) >> putStrLn "") es
    (Left err, _) -> print err
