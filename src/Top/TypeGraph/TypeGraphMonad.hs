-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphMonad 
   ( createGroup, removeGroup, updateGroupOf, getGroupOf, getAllGroups
   , TypeGraphState, HasTG(..)
   , getPossibleInconsistentGroups, addPossibleInconsistentGroup, setPossibleInconsistentGroups
   , setHeuristics, getHeuristics, nextConstraintNumber
   )
 where

import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.Basics
import Top.States.States
import Top.TypeGraph.Heuristics (Heuristic)
import Top.TypeGraph.DefaultHeuristics (defaultHeuristics)
import Data.Maybe
import Data.FiniteMap
import Data.List
import Control.Monad
import Utils (internalError)

data TypeGraphState info = TG
   { referenceMap            :: FiniteMap VertexId Int{- group number -}
   , equivalenceGroupMap     :: FiniteMap Int (EquivalenceGroup info)
   , equivalenceGroupCounter :: Int
   , possibleErrors          :: [VertexId]
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

class Monad m => HasTG m info | m -> info where
   tgGet :: m (TypeGraphState info)
   tgPut :: TypeGraphState info -> m ()  
   
tgModify :: HasTG m info => (TypeGraphState info -> TypeGraphState info) -> m ()
tgModify f = do a <- tgGet ; tgPut (f a)

tgGets :: HasTG m info => (TypeGraphState info -> a) -> m a
tgGets f = do a <- tgGet ; return (f a)

-----------------------------------------------------------------

createGroup :: HasTG m info => EquivalenceGroup info -> m ()
createGroup eqgroup =
   case vertices eqgroup of
      [] -> internalError "Top.TypeGraph.TypeGraphMonad" "createNewGroup" "cannot create an empty equivalence group"
      vs -> tgModify
               (\groups -> let newGroupNumber = equivalenceGroupCounter groups
                               list = [(i, newGroupNumber) | (i, _) <- vs ]
                           in groups { referenceMap            = addListToFM (referenceMap groups) list
                                     , equivalenceGroupMap     = addToFM (equivalenceGroupMap groups) newGroupNumber eqgroup
                                     , equivalenceGroupCounter = newGroupNumber + 1
                                     })

removeGroup :: HasTG m info => EquivalenceGroup info -> m ()                            
removeGroup eqgroup = 
   tgModify
      (\groups -> let vertexIds  = map fst (vertices eqgroup)
                      oldGroupNr = maybe [] (:[]) (lookupFM (referenceMap groups) (head vertexIds))
                  in groups { referenceMap        = delListFromFM (referenceMap groups) vertexIds -- is not necessary
                            , equivalenceGroupMap = delListFromFM (equivalenceGroupMap groups) oldGroupNr
                            })

updateGroupOf :: HasTG m info => VertexId -> (EquivalenceGroup info -> EquivalenceGroup info) -> m ()
updateGroupOf vid f = 
   do eqgrp <- getGroupOf vid
      tgModify 
         (\groups -> let err  = internalError "Top.TypeGraph.TypeGraphMonad" "updateEquivalenceGroupOf" ("error in lookup map: "++show vid)
                         eqnr = lookupWithDefaultFM (referenceMap groups) err vid
                     in groups { equivalenceGroupMap = addToFM (equivalenceGroupMap groups) eqnr (f eqgrp) })

getGroupOf :: HasTG m info => VertexId -> m (EquivalenceGroup info)                   
getGroupOf vid =
   do maybeNr <- tgGets (flip lookupFM vid . referenceMap)
      case maybeNr of 
         Nothing ->
            do let eqgroup = insertVertex vid (VVar,Nothing) emptyGroup
               createGroup eqgroup
               return eqgroup
         Just eqnr -> 
            let err = internalError "Top.TypeGraph.TypeGraphMonad" "equivalenceGroupOf" "error in lookup map"
            in tgGets (\x -> lookupWithDefaultFM (equivalenceGroupMap x) err eqnr)     

getAllGroups :: HasTG m info => m [EquivalenceGroup info]
getAllGroups = tgGets (eltsFM . equivalenceGroupMap) 

-----------------------------------------------------------------------------------

getPossibleInconsistentGroups :: HasTG m info => m [VertexId]
getPossibleInconsistentGroups = tgGets possibleErrors

setPossibleInconsistentGroups :: HasTG m info => [VertexId] -> m ()
setPossibleInconsistentGroups vids = tgModify (\x -> x { possibleErrors = vids })
      
addPossibleInconsistentGroup :: HasTG m info => VertexId -> m ()
addPossibleInconsistentGroup vid = tgModify (\x -> x { possibleErrors = vid : possibleErrors x })
         
--------------------------------------------------------------------------------

setHeuristics :: HasTG m info => [Heuristic info] -> m ()
setHeuristics hs = 
   tgModify (\x -> x {typegraphHeuristics = hs})

getHeuristics :: HasTG m info => m [Heuristic info]
getHeuristics = tgGets typegraphHeuristics

--------------------------------------------------------------------------------

nextConstraintNumber :: HasTG m info => m EdgeNr
nextConstraintNumber =
   do i <- tgGets constraintNumber
      tgModify (\x -> x { constraintNumber = constraintNumber x + 1})
      return (makeEdgeNr i)