module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)

typecheckText :: Int -> Text -> IO ()
typecheckText v expr = do
  case runStack (typecheck (readExpr expr)) v of
    (Right expr, _) -> print expr
    (Left err, _) -> print err
