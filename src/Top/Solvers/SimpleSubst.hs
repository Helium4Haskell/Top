-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.SimpleSubst (SimpleState, simpleState, HasSimple(..) ) where

import Top.Types
import Data.FiniteMap
import Top.States.States
import Top.States.SubstState
import Top.States.BasicState
import Top.States.TIState

type SimpleState = FiniteMapSubstitution

instance Show SimpleState where
   show _ = "<Simple Substitution>"

instance Empty SimpleState where
   empty = emptySubst

instance IsState SimpleState

class HasSubst m info => HasSimple m info | m -> info where
   simpleGet :: m SimpleState
   simplePut :: SimpleState -> m ()

simpleModify f = do a <- simpleGet ; simplePut (f a)
simpleGets   f = do a <- simpleGet ; return (f a)
     
simpleState :: (HasBasic m info, HasTI m info, HasSimple m info) => SubstState m info
simpleState = SubstState 
   { 
     makeConsistent_impl = 
        return ()
       
   , unifyTerms_impl = \info t1 t2 ->
        do synonyms <- getTypeSynonyms
           t1'      <- applySubst t1
           t2'      <- applySubst t2
           case mguWithTypeSynonyms synonyms t1' t2' of
              Right (used,sub) -> 
                 simpleModify (sub @@)
              Left _ -> addLabeledError unificationErrorLabel info
          
   , findSubstForVar_impl = \i ->      
       simpleGets (lookupInt i)
          
   , fixpointSubst_impl = 
        simpleGets FixpointSubstitution  
   }
