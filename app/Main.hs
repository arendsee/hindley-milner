{-# LANGUAGE QuasiQuotes #-}

module Main where

import Xi
import Xi.Util((<>))

import System.Console.Docopt
import qualified System.Environment as SE
import qualified Data.Text as T
import qualified Data.Text.IO as DIO
import qualified System.FilePath.Posix as SFP

template :: Docopt
template = [docoptFile|USAGE|]

getArgOrExit :: Arguments -> Option -> IO String
getArgOrExit = getArgOrExitWith template

-- do not check existence of source files
ignoreSource :: T.Text -> IO () 
ignoreSource _ = return ()

localModules :: Maybe String -> MVar -> IO T.Text
localModules (Just filename) (MV f)
  = DIO.readFile
  . SFP.replaceFileName filename
  $ (T.unpack f <> ".loc")
localModules Nothing (MV f) = DIO.readFile (T.unpack f <> ".loc")

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
    fmap typecheck (parse ignoreSource (localModules base) expr') >>= writer
