module Xi (typecheckText) where

import Xi.Infer 
import Xi.Data
import Xi.Parser
import Data.Text (Text)
import Data.Text.Prettyprint.Doc

typecheckText :: Int -> Text -> IO ()
typecheckText verbosity expr = do
      t <- runStack (typecheck (readExpr expr)) verbosity
      if verbosity > 0
      then case t of
        (Right t) -> print (pretty t)
        (Left err) -> print (pretty err)
      else print "ERROR: Verbosity must be greater than 0"
