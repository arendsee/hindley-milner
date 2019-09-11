module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

typecheckText :: Text -> IO ()
typecheckText expr = do
  case runStack (typecheck (readProgram expr)) of
    (Right es, _) -> mapM_ (\e -> putDoc (prettyModule e) >> putStrLn "") es
    (Left err, _) -> print err
