module State
( 
    Infer
  , newname
  , initState
) where

import qualified Control.Monad.State as MS
import Control.Monad (replicateM)

data HMState = HMState { index :: Int }

type Name = String
type Infer = MS.State HMState;

initState :: HMState
initState = HMState { index = 0 }

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

newname :: Infer Name 
newname = do
  s <- MS.get
  let v = letters !! index s
  MS.put (s {index = index s + 1})
  return v
