{-# LANGUAGE QuasiQuotes #-}

module Main where

import Xi
import Xi.Parser (readType)

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
  expr <- fmap pack $ getArgOrExit args (argument "expression")
  if isPresent args (longOption "type")
  then
    print $ readType expr
  else
    typecheckText expr
