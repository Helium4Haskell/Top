-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.States.SubstState where

import Top.Types

class Monad m => HasSubst m info | m -> info where
   substState :: SubstState m info
   
data SubstState m info = SubstState
   { makeConsistent_impl  :: m ()
   , unifyTerms_impl      :: info -> Tp -> Tp -> m ()
   , findSubstForVar_impl :: Int -> m Tp
   , fixpointSubst_impl   :: m FixpointSubstitution
   }

---------------------------------------------------------------------
-- substitution

makeConsistent    :: HasSubst m info => m ()
unifyTerms        :: HasSubst m info => info -> Tp -> Tp -> m ()
findSubstForVar   :: HasSubst m info => Int -> m Tp
fixpointSubst     :: HasSubst m info => m FixpointSubstitution     
applySubst        :: (Substitutable a, HasSubst m info) => a -> m a

makeConsistent  = makeConsistent_impl substState
unifyTerms      = unifyTerms_impl substState 
findSubstForVar = findSubstForVar_impl substState 
fixpointSubst   = fixpointSubst_impl substState                    
                           
applySubst a = 
   do let var = ftv a
      tps <- mapM findSubstForVar var
      let sub = listToSubstitution (zip var tps)                          
      return (sub |-> a)
