module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

typecheckText :: Int -> Text -> IO ()
typecheckText v expr = do
      e <- runStack (typecheck (readExpr expr)) v
      if v > 0
      then case e of
        (Right expr') -> putDoc (prettyExpr expr') >> putStrLn ""
        (Left err) -> print (pretty err)
      else putStrLn "ERROR: Verbosity must be greater than 0"
