-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An extendable state monad that contains a BasicState.
--
-----------------------------------------------------------------------------

module Top.Solvers.BasicMonad where

import Top.Constraints.Constraints
import Top.States.BasicState
import Top.States.States
import qualified Control.Monad.State as M

---------------------------------------------------------------------
-- * A basic state monad 

-- |An extendable monad containing a BasicState.
newtype BasicX info ext result = BasicX { unBasicX :: M.State (BasicState (BasicX info ext) info, ext) result }
-- |A monad containing a BasicState that cannot be extended anymore.
type    Basic  info = BasicX info ()

instance Monad (BasicX info ext) where
   return x       = BasicX (return x)
   BasicX f >>= g = BasicX (f >>= (unBasicX . g))

instance HasBasic (BasicX info ext) info where
   basicGet   = BasicX (M.gets fst)
   basicPut x = BasicX (M.modify (\(_,y) -> (x,y)))

-- |Get the extension.
getX :: BasicX info ext ext
getX = BasicX (M.gets snd)

-- |Get from the extension
getsX :: (ext -> a) -> BasicX info ext a
getsX f = getX >>= return . f

-- |Put the extension.
putX :: ext -> BasicX info ext ()
putX y = BasicX (M.modify (\(x,_) -> (x,y)))

-- |Modify the extension
modifyX :: (ext -> ext) -> BasicX info ext ()
modifyX f = getX >>= putX . f

-----------------------------------------------
-- * Get and put functions
{-
get1 = id
get2 = snd . get1
get3 = snd . get2
get4 = snd . get3
get5 = snd . get4
get6 = snd . get5
get7 = snd . get6
get8 = snd . get7

put1 = ($)
put2 = applySnd . put1
put3 = applySnd . put2
put4 = applySnd . put3
put5 = applySnd . put4
put6 = applySnd . put5
put7 = applySnd . put6
put8 = applySnd . put7

-- helper functions
getWith :: (a -> (b, c)) -> BasicX info a b
getWith f = getsX (fst . f) 

putWith :: (((a, b) -> (c, b)) -> d -> d) -> c -> BasicX info d ()
putWith f = modifyX . f . applyFst . const

applyFst :: (a -> a') -> (a, b) -> (a', b)
applyFst f (a, b) = (f a, b)

applySnd :: (b -> b') -> (a, b) -> (a, b')
applySnd f (a, b) = (a, f b)
-}
-- |Print the current state and add this as a debug message. 
printState :: IsState ext => BasicX info ext ()
printState = 
   do x <- basicGet
      y <- getX 
      let hline = replicate 50 '-'
      printMessage (unlines $ [hline] ++ showStates x ++ showStates y ++ [hline])

printConstraints :: IsState ext => BasicX info ext ()
printConstraints = 
   do x <- basicGet
      printMessage (unlines $ showStates x)
   
-- |Evaluation of an extended basic state is possible if we know the 
-- empty value of the extension.
eval :: IsState ext => BasicX info ext result -> result
eval basicX = 
   M.evalState (unBasicX basicX) empty   

-------------------------------

pushAndSolveConstraints :: (IsState ext, Solvable constraint (BasicX info ext)) 
                              => [constraint] -> BasicX info ext ()
pushAndSolveConstraints cs = 
   do pushConstraints (liftConstraints cs)
      printConstraints
      startSolving
      printState