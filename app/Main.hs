{-# LANGUAGE QuasiQuotes #-}

module Main where

import System.Console.Docopt
import Control.Monad (when)
import qualified System.Environment as SE
import Xi
import Data.Text.Prettyprint.Doc (pretty)
import Data.Text (pack)

template :: Docopt
template = [docoptFile|USAGE|]

getArgOrExit :: Arguments -> Option -> IO String
getArgOrExit = getArgOrExitWith template

main :: IO ()
main = do
  args <- parseArgsOrExit template =<< SE.getArgs
  let verbosityStr = getArgWithDefault args "1" (longOption "verbosity")
  expr <- fmap pack $ getArgOrExit args (argument "expression")
  case (reads verbosityStr :: [(Int, String)]) of
    [(verbosity, "")] -> typecheckText verbosity expr
    _ -> error "Expected verbosity argument to be an integer"
