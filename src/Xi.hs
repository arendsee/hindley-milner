module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal (putDoc)

typecheckText :: Int -> Text -> IO ()
typecheckText verbosity expr = do
      e <- runStack (typecheck (readExpr expr)) verbosity
      if verbosity > 0
      then case e of
        (Right e) -> putDoc (prettyExpr e) >> putStrLn ""
        (Left err) -> print (pretty err)
      else print "ERROR: Verbosity must be greater than 0"
