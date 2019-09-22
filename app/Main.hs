{-# LANGUAGE QuasiQuotes #-}

{-|
Module      : Main
Description : Executable for debugging the Morloc typechecker
Copyright   : (c) Zebulun Arendsee, 2019
License     : GPL-3
Maintainer  : zbwrnz@gmail.com
Stability   : experimental
-}

module Main where

import Xi
import Xi.Util((<>))

import System.Console.Docopt
import qualified System.Environment as SE
import qualified Data.Text as T
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
           else (return . T.pack) expr
  let base = if isPresent args (longOption "file")
             then Just expr
             else Nothing
  let writer = if isPresent args (longOption "raw") then ugly else cute

  if isPresent args (longOption "type")
  then
    print $ readType expr'
  else
    fmap typecheck (parse ignoreSource (localModules base) (fmap T.pack base) expr') >>= writer
