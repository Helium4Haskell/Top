-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphSubst where

import Top.States.SubstState
import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Basics
import Top.Types
import Control.Monad
import Data.FiniteMap
       
typegraphImpl :: HasTypeGraph m info => SubstState m info
typegraphImpl = SubstState
   { 
     makeConsistent_impl = 
        debugTrace "makeConsistent" >>
        do removeInconsistencies   
       
   , unifyTerms_impl = \info t1 t2 ->
        debugTrace ("unifyTerms "++show t1++" "++show t2) >>
        do v1 <- makeTermGraph t1
           v2 <- makeTermGraph t2     
           addNewEdge (EdgeID v1 v2) info
           
   , findSubstForVar_impl = \i ->      
        debugTrace ("findSubstForVar " ++ show i) >>
        do tp <- substForVar_nr i
           case tp of
              -- in case of an application, recurse
              TApp l r ->
                 do l' <- applySubst l
                    r' <- applySubst r
                    return (TApp l' r')
              _ -> return tp
            
   , fixpointSubst_impl =         
        debugTrace ("fixpointSubstitution") >>
        do xs <- makeSubstitution
           return (FixpointSubstitution (listToFM xs))
   }
