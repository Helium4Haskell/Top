-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A state that contains a substitution 
--
-----------------------------------------------------------------------------

module Top.States.SubstState where

import Top.Types

---------------------------------------------------------------------
-- * Substitution state

-- |A type class for states that contain a substitution.
class Monad m => HasSubst m info | m -> info where
   substState :: SubstState m info

-- |The four methods that should be provided. The methods are packed into a datatype 
-- to make it easier to use implementations in all kinds of states.   
data SubstState m info = SubstState    
   { makeConsistent_impl  :: m ()
   , unifyTerms_impl      :: info -> Tp -> Tp -> m () 
   , findSubstForVar_impl :: Int -> m Tp
   , fixpointSubst_impl   :: m FixpointSubstitution
   }

---------------------------------------------------------------------
-- * Substitution methods

-- |Make the state consistent. Only relevant for substitution states that 
-- can be inconsistent (for instance, the type graph substitution state).
makeConsistent    :: HasSubst m info => m ()
-- |Unify two terms. Supply additional information for this unification.
unifyTerms        :: HasSubst m info => info -> Tp -> Tp -> m ()
-- |Lookup the value of a type variable in the substitution
findSubstForVar   :: HasSubst m info => Int -> m Tp
-- |Return a fixpoint substitution.
fixpointSubst     :: HasSubst m info => m FixpointSubstitution    
-- |Apply the substitution to a value that contains type variables (a 
-- member of the Substitutable type class). 
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
