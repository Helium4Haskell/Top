-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An extendable state monad that contains a BasicState.
--
-----------------------------------------------------------------------------

module Top.States.BasicMonad where

import Top.States.BasicState
import Control.Monad.State

---------------------------------------------------------------------
-- * A basic state monad 

-- |An extendable monad containing a BasicState.
newtype BasicX info ext result = BasicX { unBasicX :: State (BasicState (BasicX info ext) info, ext) result }
-- |A monad containing a BasicState that cannot be extended anymore.
type    Basic  info = BasicX info ()

instance Monad (BasicX info ext) where
   return x       = BasicX (return x)
   BasicX f >>= g = BasicX (f >>= (unBasicX . g))

instance HasBasic (BasicX info ext) info where
   basicGet   = BasicX (gets fst)
   basicPut x = BasicX (modify (\(_,y) -> (x,y)))

-- |Get the extension.
getX :: BasicX info ext ext
getX = BasicX (gets snd)

-- |Put the extension.
putX :: ext -> BasicX info ext ()
putX y = BasicX (modify (\(x,_) -> (x,y)))

---------------------------------------------------------------------
-- * A type class for states.

class Show a => IsState a where
   empty      :: a                  -- ^ The empty (initial) value
   showStates :: a -> [String]      -- ^ Show this state, and all states that are contained by this state.
                                    -- By default, use the show function from the Show type class.
   showStates a = [show a]

instance IsState () where
   empty         = ()
   showStates () = []

instance (IsState a, IsState b) => IsState (a, b) where 
   empty = (empty, empty)
   showStates (a,b) = showStates a++showStates b

instance IsState (BasicState m info) where 
   empty = emptyBasic   

-- |Print the current state and add this as a debug message. 
printState :: IsState ext => BasicX info ext ()
printState = 
   do x <- basicGet
      y <- getX 
      let hline = replicate 50 '-'
      printMessage (unlines $ [hline] ++ showStates x ++ showStates y ++ [hline])

-- |Evaluation of an extended basic state is possible if we know the 
-- empty value of the extension.
eval :: IsState ext => BasicX info ext result -> result
eval basicX = 
   evalState (unBasicX basicX) empty   
