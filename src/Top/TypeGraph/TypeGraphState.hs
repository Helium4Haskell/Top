-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphState where

import Top.TypeGraph.Basics
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.Types
import Data.List 
import qualified Data.Set as S
import Utils (internalError)
import Control.Monad
                   
class (HasBasic m info, HasTI m info, HasSubst m info)
         => HasTypeGraph m info | m -> info where          
   
   -- construct a type graph
   addTermGraph :: Tp -> m VertexID
   addVertex    :: VertexID -> VertexInfo -> m ()
   addEdge      :: EdgeID -> EdgeInfo info ->  m ()
   
   -- deconstruct a type graph
   deleteEdge :: EdgeID -> m () 
   
   -- inspect an equivalence group in a type graph
   verticesInGroupOf       :: VertexID -> m [(VertexID, VertexInfo)]
   childrenInGroupOf       :: VertexID -> m ([ParentChild], [ParentChild])
   constantsInGroupOf      :: VertexID -> m [String]
   representativeInGroupOf :: VertexID -> m VertexID
   edgesFrom               :: VertexID -> m [(EdgeID, EdgeNr, info)]
   
   -- query a path in an equivalence group
   allPaths            :: VertexID -> VertexID -> m (TypeGraphPath info)
   allPathsList        :: VertexID -> [VertexID] -> m (TypeGraphPath info)
   allPathsListWithout :: S.Set VertexID -> VertexID -> [VertexID] -> m (TypeGraphPath info)  
   
   -- make the type graph consistent
   removeInconsistencies :: m ()
   
   -- substitution and term graph
   substituteVariable :: VertexID -> m Tp
   makeSubstitution   :: m [(VertexID, Tp)]
   typeFromTermGraph  :: VertexID -> m Tp
   
   -- Extra administration
   nextConstraintNumber    :: m EdgeNr
   markAsPossibleError     :: VertexID -> m ()
   getMarkedPossibleErrors :: m [VertexID]
   unmarkPossibleErrors    :: m ()
   
   -------------------------------------------
   -- default definitions   
   
   allPaths i1 i2 = 
      allPathsList i1 [i2]
   allPathsList = 
      allPathsListWithout S.emptySet
      
   childrenInGroupOf i =
      do vs <- verticesInGroupOf i 
         return $ unzip 
            [ ( ParentChild { parent=p, child = t1, childSide=LeftChild  }
              , ParentChild { parent=p, child = t2, childSide=RightChild } 
              ) 
            | (p, (VApp t1 t2, _)) <- vs 
            ]
             
   constantsInGroupOf i = 
      do vs <- verticesInGroupOf i 
         return (nub [ s | (_, (VCon s, _)) <- vs ])
      
   representativeInGroupOf i =
      do vs <- verticesInGroupOf i
         case vs of 
            (vid, _):_ -> return vid
            _ -> internalError "Top.TypeGraph.TypeGraphState" "representativeInGroupOf" "unexpected empty equivalence group"