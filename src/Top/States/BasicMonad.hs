-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.States.BasicMonad where

import Top.States.BasicState
import Control.Monad.State

---------------------------------------------------------------------
-- A basic state monad 

newtype BasicX info ext result = BasicX { unBasicX :: State (BasicState (BasicX info ext) info, ext) result }
type    Basic  info = BasicX info ()

instance Monad (BasicX info ext) where
   return x       = BasicX (return x)
   BasicX f >>= g = BasicX (f >>= (unBasicX . g))

instance HasBasic (BasicX info ext) info where
   basicGet   = BasicX (gets fst)
   basicPut x = BasicX (modify (\(_,y) -> (x,y)))

getX :: BasicX info ext ext
getX = BasicX (gets snd)

putX :: ext -> BasicX info ext ()
putX y = BasicX (modify (\(x,_) -> (x,y)))

---------------------------------------------------------------------
-- A class for empty (or: default) values

class Show a => IsState a where
   empty      :: a
   showStates :: a -> [String]   
   showStates a = [show a]

instance IsState () where
   empty         = ()
   showStates () = []

instance (IsState a, IsState b) => IsState (a, b) where 
   empty = (empty, empty)
   showStates (a,b) = showStates a++showStates b

instance IsState (BasicState m info) where 
   empty = emptyBasic   

printState :: IsState ext => BasicX info ext ()
printState = 
   do x <- basicGet
      y <- getX 
      let hline = replicate 50 '-'
      printMessage (unlines $ [hline] ++ showStates x ++ showStates y ++ [hline])

---------------------------------------------------------------------
-- Evaluation of an extended basic state is possible if we know the 
-- empty value of the extension

eval :: IsState ext => BasicX info ext result -> result
eval basicX = 
   evalState (unBasicX basicX) empty   
