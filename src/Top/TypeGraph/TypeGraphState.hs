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
   addTermGraph :: Tp -> m VertexId
   addVertex    :: VertexId -> VertexInfo -> m ()
   addEdge      :: EdgeId -> EdgeInfo info ->  m ()
   
   -- deconstruct a type graph
   deleteEdge :: EdgeId -> m ()
   
   -- inspect an equivalence group in a type graph
   verticesInGroupOf       :: VertexId -> m [(VertexId, VertexInfo)]
   childrenInGroupOf       :: VertexId -> m ([ParentChild], [ParentChild])
   constantsInGroupOf      :: VertexId -> m [String]
   representativeInGroupOf :: VertexId -> m VertexId
   edgesFrom               :: VertexId -> m [(EdgeId, EdgeNr, info)]
   
   -- query a path in an equivalence group
   allPaths            :: VertexId -> VertexId -> m (TypeGraphPath info)
   allPathsList        :: VertexId -> [VertexId] -> m (TypeGraphPath info)
   allPathsListWithout :: S.Set VertexId -> VertexId -> [VertexId] -> m (TypeGraphPath info)  
   
   -- make the type graph consistent
   removeInconsistencies :: m ()
   
   -- substitution and term graph
   substituteVariable :: Int -> m Tp
   substituteType     :: Tp  -> m Tp
   substituteTypeSafe :: Tp  -> m (Maybe Tp)
   makeSubstitution   :: m [(VertexId, Tp)]
   typeFromTermGraph  :: VertexId -> m Tp
   
   -- Extra administration
   markAsPossibleError     :: VertexId -> m ()
   getMarkedPossibleErrors :: m [VertexId]
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
            
   substituteVariable =
      substituteType . TVar
      
   substituteType tp =
      do mtp <- substituteTypeSafe tp
         case mtp of
            Just stp -> return stp
            Nothing  -> internalError "Top.TypeGraph.TypeGraphState" "substituteType" "inconsistent state"