{-# LANGUAGE QuasiQuotes #-}

module Main where

import Xi
import Xi.Parser (readType)

import System.Console.Docopt
import qualified System.Environment as SE
import qualified Data.Text as DT
import qualified Data.Text.IO as DIO

template :: Docopt
template = [docoptFile|USAGE|]

getArgOrExit :: Arguments -> Option -> IO String
getArgOrExit = getArgOrExitWith template

main :: IO ()
main = do
  args <- parseArgsOrExit template =<< SE.getArgs
  expr <- getArgOrExit args (argument "code")
  expr' <- if isPresent args (longOption "file")
           then DIO.readFile expr
           else (return . DT.pack) expr
  if isPresent args (longOption "type")
  then
    print $ readType expr'
  else
    if isPresent args (longOption "raw")
    then
      ugly expr'
    else 
      cute expr'
