-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.Heuristics where

import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
import Top.Types
import Control.Monad
import Utils (internalError)

-----------------------------------------------------------------------------

newtype Heuristic  info = Heuristic (forall m . HasTypeGraph m info => HComponent m info)
data HasTypeGraph m info => Selector m info 
   = Selector       (String, (EdgeId, EdgeNr, info) -> m (Maybe (Int, String, [EdgeId], [info])))
   | SelectorList   (String, [(EdgeId, EdgeNr, info)] -> m (Maybe (Int, String, [EdgeId], [info])))
   | SelectorAction (String, (EdgeId, EdgeNr, info) -> m (Maybe (m (), Int, String, [EdgeId], [info])))
   | SelectorPath   (Path (EdgeId, EdgeNr, info) -> Selector m info)

data HComponent m info 
     = Filter    String ([(EdgeId, EdgeNr, info)] -> m [(EdgeId, EdgeNr, info)])
     | Voting   [Selector m info]
     | PathComponent (Path (EdgeId, EdgeNr, info) -> Heuristic info)
          
resultsEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((EdgeId,EdgeNr,info) -> m a) -> HComponent m info
resultsEdgeFilter selector description function =
   Filter description $ \es -> 
   do tupledList <- let f tuple = 
                           do result <- function tuple
                              return (result, tuple)
                    in mapM f es
      let maximumResult 
            | null tupledList = internalError "Top.TypeGraph.Heuristics" "resultsEdgeFilter" "unexpected empty list" 
            | otherwise       = selector (map fst tupledList)
      return (map snd (filter ((maximumResult ==) . fst) tupledList))

maximalEdgeFilter :: (Ord a, Monad m) => String -> ((EdgeId,EdgeNr,info) -> m a) -> HComponent m info
maximalEdgeFilter = resultsEdgeFilter maximum

minimalEdgeFilter :: (Ord a, Monad m) => String -> ((EdgeId,EdgeNr,info) -> m a) -> HComponent m info
minimalEdgeFilter = resultsEdgeFilter minimum

edgeFilter :: Monad m => String -> ((EdgeId, EdgeNr, info) -> m Bool) -> HComponent m info
edgeFilter description function = 
   Filter description $ \es -> 
      do xs <- filterM function es
         return (if (null xs) then es else xs)


-----------------------------------------------------------------------------

doWithoutEdges :: HasTypeGraph m info => [(EdgeId, EdgeNr, info)] -> m result -> m result
doWithoutEdges xs computation = 
   case xs of 
      []   -> computation
      [e]  -> doWithoutEdge e computation
      e:es -> doWithoutEdge e (doWithoutEdges es computation)

doWithoutEdge :: HasTypeGraph m info => (EdgeId, EdgeNr, info) -> m result -> m result
doWithoutEdge (edge, cnr, info) computation =
   debugTrace ("doWithoutEdge " ++ show edge)  >> 
   do -- copy1 <- mapM showGroupOf [0..100]
      deleteEdge edge       
      result <- computation           
      addEdge edge (cnr, info)
      -- copy2 <- mapM showGroupOf [0..100]
      -- if copy1 /= copy2 then 
      --   error ("SAFETY check failed\n\n" ++ head [ x1++x2 | (x1, x2) <- zip copy1 copy2, x1 /= x2]) else
      return result

eqInfo3 :: (EdgeId, EdgeNr, info) -> (EdgeId, EdgeNr, info) -> Bool
eqInfo3 (_, b1, _) (_, b2, _) = b1 == b2

info3ToEdgeNr :: (EdgeId, EdgeNr, info) -> EdgeNr
info3ToEdgeNr (_, i, _) = i

-----------------------------------------------------------------------------

class HasTwoTypes a where
   getTwoTypes :: a -> (Tp, Tp)

getSubstitutedTypes :: (HasTypeGraph m info, HasTwoTypes info) => info -> m (Maybe Tp, Maybe Tp)
getSubstitutedTypes info = 
   do let (t1,t2) = getTwoTypes info
      mt1 <- substituteTypeSafe t1
      mt2 <- substituteTypeSafe t2
      return (mt1, mt2)
