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
import Top.TypeGraph.TypeGraphMonad
import Top.TypeGraph.Basics
import Top.Types
import Control.Monad
import Data.FiniteMap
       
typegraphImpl :: (HasTG m info, HasTypeGraph m info) => SubstState m info
typegraphImpl = SubstState
   { 
     makeConsistent_impl = 
        debugTrace "makeConsistent" >>
        removeInconsistencies   
       
   , unifyTerms_impl = \info t1 t2 ->
        debugTrace ("unifyTerms "++show t1++" "++show t2) >>
        do v1  <- addTermGraph t1
           v2  <- addTermGraph t2
           cnr <- nextConstraintNumber           
           addEdge (EdgeId v1 v2) (cnr, info)
           
   , findSubstForVar_impl = \i ->      
        debugTrace ("findSubstForVar " ++ show i) >>
        substituteVariable i
            
   , fixpointSubst_impl =         
        debugTrace ("fixpointSubstitution") >>
        do xs <- makeSubstitution
           let list = [ (i, tp) | (VertexId i, tp) <- xs ]
           return (FixpointSubstitution (listToFM list))
   }
