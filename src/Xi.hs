module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

typecheckText :: Int -> Text -> IO ()
typecheckText v expr = do
  case runStack (typecheck (readExpr expr)) v of
    (Right expr, _) -> putDoc (prettyExpr expr) >> putStrLn ""
    (Left err, _) -> print err
