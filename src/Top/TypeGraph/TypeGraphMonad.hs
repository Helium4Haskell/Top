-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphMonad where

import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.Basics
import Top.States.States
import Top.States.SubstState
import Top.TypeGraph.Heuristics (Heuristic)
import Top.TypeGraph.DefaultHeuristics (defaultHeuristics)
import Data.Maybe
import Data.FiniteMap
import Control.Monad
import Utils (internalError)

data TypeGraphState info = TG
   { referenceMap            :: FiniteMap VertexID Int {- group number -}
   , equivalenceGroupMap     :: FiniteMap Int (EquivalenceGroup info)
   , equivalenceGroupCounter :: Int
   , possibleErrors          :: [VertexID]
   , typegraphHeuristics     :: [Heuristic info]
   , constraintNumber        :: Int
   } 

instance Show info => Empty (TypeGraphState info) where
   empty = TG
      { referenceMap            = emptyFM
      , equivalenceGroupMap     = emptyFM
      , equivalenceGroupCounter = 0
      , possibleErrors          = []
      , typegraphHeuristics     = defaultHeuristics
      , constraintNumber        = 0
      }

instance Show (TypeGraphState info) where
   show _ = "<TypeGraphState>"

instance Show info => IsState (TypeGraphState info)

class HasSubst m info => HasTG m info | m -> info where
   tgGet :: m (TypeGraphState info)
   tgPut :: TypeGraphState info -> m ()  
   
tgModify :: HasTG m info => (TypeGraphState info -> TypeGraphState info) -> m ()
tgModify f = do a <- tgGet ; tgPut (f a)

tgGets :: HasTG m info => (TypeGraphState info -> a) -> m a
tgGets f = do a <- tgGet ; return (f a)

-----------------------------------------------------------------

createNewGroup :: HasTG m info => EquivalenceGroup info -> m Int
createNewGroup eqgroup =
   do tgModify
         (\groups -> let newGroupNumber = equivalenceGroupCounter groups
                         list = [(i, newGroupNumber) | (i, _) <- vertices eqgroup]
                     in groups { referenceMap            = addListToFM (referenceMap groups) list
                               , equivalenceGroupMap     = addToFM (equivalenceGroupMap groups) newGroupNumber eqgroup
                               , equivalenceGroupCounter = newGroupNumber + 1
                               })
      case vertices eqgroup of
         (vid,_):_ -> return vid
         _ -> internalError "Top.TypeGraph.TypeGraphMonad" "createNewGroup" "cannot create an empty equivalence group"
                            
removeGroup :: HasTG m info => EquivalenceGroup info -> m ()                            
removeGroup eqgroup = 
   tgModify
      (\groups -> let vertexIDs  = map fst (vertices eqgroup)
                      oldGroupNr = maybe [] (:[]) (lookupFM (referenceMap groups) (head vertexIDs))
                  in groups { referenceMap        = delListFromFM (referenceMap groups) vertexIDs -- is not necessary
                            , equivalenceGroupMap = delListFromFM (equivalenceGroupMap groups) oldGroupNr
                            })

updateEquivalenceGroupOf :: HasTG m info => Int -> (EquivalenceGroup info -> EquivalenceGroup info) -> m ()
updateEquivalenceGroupOf i f = 
   do eqgrp <- equivalenceGroupOf i 
      tgModify 
         (\groups -> let err  = internalError "Top.TypeGraph.TypeGraphMonad" "updateEquivalenceGroupOf" "error in lookup map"
                         eqnr = lookupWithDefaultFM (referenceMap groups) err i
                     in groups { equivalenceGroupMap = addToFM (equivalenceGroupMap groups) eqnr (f eqgrp) })

equivalenceGroupOf :: HasTG m info => Int -> m (EquivalenceGroup info)                   
equivalenceGroupOf i =
   do maybeNr <- tgGets (flip lookupFM i . referenceMap)
      case maybeNr of 
         Nothing ->
            return (insertVertex i (VVar,Nothing) emptyGroup)
         Just eqnr -> 
            let err = internalError "Top.TypeGraph.TypeGraphMonad" "equivalenceGroupOf" "error in lookup map"
            in tgGets (\x -> lookupWithDefaultFM (equivalenceGroupMap x) err eqnr)     
            
areInTheSameGroup :: HasTG m info => Int -> Int -> m Bool
areInTheSameGroup v1 v2 =
   tgGets
      (\groups -> let eqnr1 = lookupFM (referenceMap groups) v1
                      eqnr2 = lookupFM (referenceMap groups) v2
                  in eqnr1 == eqnr2 && isJust eqnr1)
            
-----------------------------------------------------------------------------------

getPossibleErrors :: HasTG m info => m [VertexID]
getPossibleErrors = tgGets possibleErrors

setPossibleErrors :: HasTG m info => [VertexID] -> m ()
setPossibleErrors vids = tgModify (\x -> x { possibleErrors = vids })
      
addPossibleError :: HasTG m info => VertexID -> m ()
addPossibleError vid = tgModify (\x -> x { possibleErrors = vid : possibleErrors x })

-----------------------------------------------------------------------------------

nextConstraintNumber :: HasTG m info => m Int
nextConstraintNumber = 
   do i <- tgGets constraintNumber
      tgModify (\x -> x { constraintNumber = constraintNumber x + 1})
      return i
         
--------------------------------------------------------------------------------

setHeuristics :: HasTG m info => [Heuristic info] -> m ()
setHeuristics hs = 
   tgModify (\x -> x {typegraphHeuristics = hs})

----------------------------------------------------------------------------------

combineClasses :: HasTG m info => Int -> Int -> m ()
combineClasses v1 v2 =
   debugTrace ("combineClasses " ++ show v1 ++ " " ++ show v2) >>
   do condition <- areInTheSameGroup v1 v2
      unless condition $ 
         do eqc1 <- equivalenceGroupOf v1
            eqc2 <- equivalenceGroupOf v2
            removeGroup eqc1
            removeGroup eqc2
            createNewGroup (combineGroups eqc1 eqc2)  
            addPossibleError v1
           
