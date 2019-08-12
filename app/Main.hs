{-# LANGUAGE QuasiQuotes #-}

module Main where

import System.Console.Docopt
import Control.Monad (when)
import qualified System.Environment as SE
import Bidirectional.Dunfield.Infer
import Bidirectional.Dunfield.Data
import Bidirectional.Dunfield.Parser
import Data.Text.Prettyprint.Doc (pretty)

template :: Docopt
template = [docoptFile|USAGE|]

getArgOrExit :: Arguments -> Option -> IO String
getArgOrExit = getArgOrExitWith template

main :: IO ()
main = do
  args <- parseArgsOrExit template =<< SE.getArgs
  let verbosityStr = getArgWithDefault args "1" (longOption "verbosity")
  expr <- getArgOrExit args (argument "expression")
  case (reads verbosityStr :: [(Int, String)]) of
    [(verbosity, "")] -> do
      t <- runStack (typecheck (readExpr expr)) verbosity
      if verbosity > 0
      then case t of
        (Right t) -> print (pretty t)
        (Left err) -> print (pretty err)
      else return ()
    _ -> error "Expected verbosity argument to be an integer"
