-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.GreedySubst (GreedyState, emptyGreedy, greedyState, HasGreedy(..) ) where

import Top.States.SubstState
import Top.States.BasicState
import Top.States.TIState
import Top.Solvers.SolveConstraints (reducePredicates)
import Top.Types
import Data.FiniteMap
import Utils (internalError)

type GreedyState = FixpointSubstitution

emptyGreedy :: GreedyState
emptyGreedy = FixpointSubstitution emptyFM

class HasSubst m info => HasGreedy m info | m -> info where
   greedyGet :: m FixpointSubstitution
   greedyPut :: FixpointSubstitution -> m ()

greedyModify f = do a <- greedyGet ; greedyPut (f a)
greedyGets   f = do a <- greedyGet ; return (f a)

greedyState :: (HasBasic m info, HasTI m info, HasGreedy m info) => SubstState m info
greedyState = SubstState 
   { 
     makeConsistent_impl = 
        reducePredicates
   
   , unifyTerms_impl = \info t1 t2 ->
        do t1'      <- applySubst t1
           t2'      <- applySubst t2
           synonyms <- getTypeSynonyms
           case mguWithTypeSynonyms synonyms t1' t2' of        
              Left _           -> addError info        
              Right (used,sub) -> 
                 let utp = equalUnderTypeSynonyms synonyms (sub |-> t1') (sub |-> t2') 
                     f (FixpointSubstitution fm) =
                           FixpointSubstitution (addListToFM fm [ (i, lookupInt i sub) | i <- dom sub ])
                     g = writeExpandedType synonyms t2 utp 
                       . writeExpandedType synonyms t1 utp 
                     h = if used then g . f else f
                 in greedyModify h
            
   , findSubstForVar_impl = \i ->      
        greedyGets (lookupInt i)
          
   , fixpointSubst_impl = 
        greedyGet 
   }
           
-- The key idea is as follows:
-- try to minimize the number of expansions by type synonyms.
-- If a type is expanded, then this should be recorded in the substitution. 
-- Invariant of this function should be that "atp" (the first type) can be
-- made equal to "utp" (the second type) with a number of type synonym expansions             
writeExpandedType :: OrderedTypeSynonyms -> Tp -> Tp -> FixpointSubstitution ->  FixpointSubstitution
writeExpandedType synonyms = writeTypeType where

   writeTypeType :: Tp -> Tp -> FixpointSubstitution -> FixpointSubstitution
   writeTypeType atp utp original@(FixpointSubstitution fm) = 
      case (leftSpine atp,leftSpine utp) of        
         ((TVar i,[]),_)                    -> writeIntType i utp original
         ((TCon s,as),(TCon t,bs)) | s == t -> foldr (uncurry writeTypeType) original (zip as bs)                   
         ((TCon s,as),_) -> 
            case expandTypeConstructorOneStep (snd synonyms) atp of
               Just atp' -> writeTypeType atp' utp original
               Nothing   -> internalError "Top.Solvers.GreedySubst" "writeTypeType" "inconsistent types(1)"      
         _               -> internalError "Top.Solvers.GreedySubst" "writeTypeType" "inconsistent types(2)"   
      
   writeIntType :: Int -> Tp -> FixpointSubstitution -> FixpointSubstitution     
   writeIntType i utp original@(FixpointSubstitution fm) = 
      case lookupFM fm i of 
         
         Nothing  -> 
            case utp of
               TVar j | i == j -> original
               otherwise       -> FixpointSubstitution (addToFM fm i utp)
               
         Just atp ->
            case (leftSpine atp,leftSpine utp) of
               ((TVar j,[]),_) -> writeIntType j utp original
               ((TCon s,as),(TCon t,bs)) | s == t -> foldr (uncurry writeTypeType) original (zip as bs)
               ((TCon s,as),_) -> case expandTypeConstructorOneStep (snd synonyms) atp of
                                     Just atp' -> writeIntType i utp (FixpointSubstitution (addToFM fm i atp'))
                                     Nothing   -> internalError "Top.Solvers.GreedySubst" "writeIntType" "inconsistent types(1)"
               _               -> internalError "Top.Solvers.GreedySubst" "writeIntType" "inconsistent types(2)"      
