{-# LANGUAGE QuasiQuotes #-}

module Main where

import Xi

import System.Console.Docopt
import qualified System.Environment as SE
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
