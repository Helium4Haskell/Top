-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphState where

import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
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
   
   -- functions to construct a typegraph
   addNewEdge :: EdgeID -> info ->         m ()
   addEdge    :: EdgeID -> (Int, info) ->  m ()
   addVertex  :: VertexID -> VertexInfo -> m ()
   addClique  :: Cliques ->                m ()
   
   -- inspect the equivalence group of a vertex
   verticesInGroupOf       :: VertexID -> m [(VertexID, VertexInfo)]
   childrenInGroupOf       :: VertexID -> m [(VertexID, (VertexID, VertexID))]
   representativeInGroupOf :: VertexID -> m VertexID
   constantsInGroupOf      :: VertexID -> m [String]
   
   -- find all edges from a vertex, and all paths between a pair of vertices
   edgesFrom           :: VertexID -> m [(EdgeID, Int, info)]
   -- newPathList         :: [VertexID] -> VertexID -> [VertexID] -> m [Path (EdgeID, EdgeInfo info)]
   allPaths            ::                   VertexID ->  VertexID  -> m (Path (EdgeID, EdgeInfo info))
   allPathsList        ::                   VertexID -> [VertexID] -> m (Path (EdgeID, EdgeInfo info))
   allPathsListWithout :: S.Set VertexID -> VertexID -> [VertexID] -> m (Path (EdgeID, EdgeInfo info))   

   -- functions to deconstruct (remove parts of) the typegraph
   deleteEdge   :: EdgeID  -> m () 
   deleteClique :: Cliques -> m ()
   
   -- functions to find/remove inconsistencies        
   removeInconsistencies         :: m ()
   getPossibleInconsistentGroups :: m [Int]
   noPossibleInconsistentGroups  :: m ()
   
   -- building a substitution from a typegraph
   makeSubstitution :: m [(VertexID, Tp)]
   substForVar_nr   :: Int -> m Tp
          
   -- default definitions   
   allPaths i1 i2    = allPathsList i1 [i2]
   allPathsList i is = mapM (allPaths i) is >>= (return . simplifyPath . altList)
      
   childrenInGroupOf i = 
      do vs <- verticesInGroupOf i 
         return [ (j, (left, right)) | (j, (VApp left right, _)) <- vs ]
   
   representativeInGroupOf i =
      debugTrace ("representativeInGroupOf " ++ show i) >>
      do vs <- verticesInGroupOf i  
         case vs of 
            (vid,_):_ -> return vid
            _ -> internalError "Top.TypeGraph.TypeGraphState" "representativeInGroupOf" "unexpected empty equivalence group"
                  
   constantsInGroupOf i = 
      do vs <- verticesInGroupOf i 
         return (nub [ s | (_,(VCon s, _)) <- vs ])
   
makeTermGraph :: HasTypeGraph m info => Tp -> m Int
makeTermGraph tp = 
   debugTrace ("makeTermGraph " ++ show tp) >>
   case leftSpine tp of 
      (TVar i, tps) -> 
         do is <- mapM makeTermGraph tps
            makeLeftSpine Nothing i is
      (TCon s, tps) ->
         do syns <- getTypeSynonyms
            is   <- mapM makeTermGraph tps
            let tp' = expandTypeConstructor (snd syns) (foldl TApp (TCon s) (map TVar is))
            if tp == tp' 
              then do i <- makeNewVertex (VCon s, Nothing)
                      makeLeftSpine Nothing i is
              else do let (a, as) = leftSpine tp' 
                      ia'  <- makeTermGraph a
                      ias' <- mapM makeTermGraph as
                      makeLeftSpine (Just (s, is)) ia' ias'                      
      _ -> internalError "Top.TypeGraph.TypeGraphState" "makeTermGraph" "error in leftSpine(1)"
      
 where 
   makeLeftSpine original i is = 
      case is of
         []    -> return i
         hd:tl -> do unique <- makeNewVertex (VApp i hd, if null tl then original else Nothing)
                     makeLeftSpine original unique tl
                     
   makeNewVertex vertexInfo =
      do unique <- nextUnique                
         addVertex unique vertexInfo
         return unique
                                   
propagateEquality :: HasTypeGraph m info => [Int] -> m ()
propagateEquality is = 
   debugTrace ("propagateEquality " ++ show is)  >> 
   rec [] is where

   rec history js
     | length list < 2 || list `elem` history = return ()
     | otherwise = 
          let f c = do rec (list : history) (map (fst . head) (snd c))
                       addClique c
          in do cliques <- lookForCliques list
                mapM_ f cliques 
     
    where list = sort (nub js)
 
lookForCliques :: HasTypeGraph m info => [Int] -> m [Cliques]
lookForCliques is = 
   debugTrace ("lookForCliques " ++ show is) >>
   do childrenList <- mapM childrenInGroupOf is
      let notEmpties = filter (not . null) childrenList  
          f selF xs  = [ (selF ns, p) | (p, ns) <- xs ]
      return [ (nr, map (f selector) notEmpties)
             | length notEmpties > 1 
             , (nr, selector) <- [(0, fst), (1, snd)]
             ]

-- |Get the type of a vertex by following child edges. Also returns the variable
-- if it is not part of the type graph.
getFullType :: HasTypeGraph m info => Int -> m Tp
getFullType i =
   do vertices <- verticesInGroupOf i
      case [ tp | (i', (tp, _)) <- vertices, i == i' ] of
         [VCon s]   -> return (TCon s)
         [VApp a b] -> 
            do ta <- getFullType a
               tb <- getFullType b
               return (TApp ta tb)
         _ -> return (TVar i)