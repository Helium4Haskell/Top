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
   = Selector       (String, (EdgeID, Int, info) -> m (Maybe (Int, String, [EdgeID], [info])))
   | SelectorList   (String, [(EdgeID, Int, info)] -> m (Maybe (Int, String, [EdgeID], [info])))
   | SelectorAction (String, (EdgeID, Int, info) -> m (Maybe (m (), Int, String, [EdgeID], [info])))
   | SelectorPath   (Path (EdgeID, Int, info) -> Selector m info)

data HComponent m info 
     = Filter    String ([(EdgeID, Int, info)] -> m [(EdgeID, Int, info)])
     | Voting   [Selector m info]
     | PathComponent (Path (EdgeID, Int, info) -> Heuristic info)
          
resultsEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((EdgeID,Int,info) -> m a) -> HComponent m info
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

maximalEdgeFilter :: (Ord a, Monad m) => String -> ((EdgeID,Int,info) -> m a) -> HComponent m info
maximalEdgeFilter = resultsEdgeFilter maximum

minimalEdgeFilter :: (Ord a, Monad m) => String -> ((EdgeID,Int,info) -> m a) -> HComponent m info
minimalEdgeFilter = resultsEdgeFilter minimum

edgeFilter :: Monad m => String -> ((EdgeID, Int, info) -> m Bool) -> HComponent m info
edgeFilter description function = 
   Filter description $ \es -> 
      do xs <- filterM function es
         return (if (null xs) then es else xs)


-----------------------------------------------------------------------------

doWithoutEdges :: HasTypeGraph m info => [(EdgeID, Int, info)] -> m result -> m result
doWithoutEdges xs computation = 
   case xs of 
      []   -> computation
      [e]  -> doWithoutEdge e computation
      e:es -> doWithoutEdge e (doWithoutEdges es computation)

doWithoutEdge :: HasTypeGraph m info => (EdgeID, Int, info) -> m result -> m result
doWithoutEdge (edge, cnr, info) computation =
   do deleteEdge edge       
      result <- computation           
      addEdge edge (cnr, info)
      return result
                   
-- keep a history to avoid non-termination (for type-graphs that contain an infinite type)
safeApplySubst :: HasTypeGraph m info => Tp -> m (Maybe Tp)
safeApplySubst = rec [] where 

  rec history tp = case tp of 
  
    TVar i | i `elem` history 
               -> return Nothing
           | otherwise 
               -> do vs       <- verticesInGroupOf  i
                     cs       <- constantsInGroupOf i
                     children <- childrenInGroupOf  i                     
                     case cs of 
                        [s] -> return (Just (TCon s))               
                        []  -> case children of 
                                  []        -> let rep = fst (head vs)
                                               in return (Just (TVar rep))
                                  (_, (c1, c2)):_ -> 
                                     do mt1 <- rec (i : history) (TVar c1)
                                        mt2 <- rec (i : history) (TVar c2)
                                        return $ 
                                           do tp1 <- mt1
                                              tp2 <- mt2
                                              return (TApp tp1 tp2)
                        _ -> return Nothing
    TCon _     -> return (Just tp)
    
    TApp t1 t2 -> do mt1 <- rec history t1
                     mt2 <- rec history t2
                     case (mt1,mt2) of 
                       (Just t1', Just t2') -> return (Just $ TApp t1' t2')
                       _                    -> return Nothing

eqInfo3 :: (EdgeID, Int, info) -> (EdgeID, Int, info) -> Bool
eqInfo3 (_, b1, _) (_, b2, _) = b1 == b2

info3ToInt :: (EdgeID, Int, info) -> Int
info3ToInt (_, i, _) = i

-----------------------------------------------------------------------------

class HasTwoTypes a where
   getTwoTypes :: a -> (Tp, Tp)

getSubstitutedTypes :: (HasTypeGraph m info, HasTwoTypes info) => info -> m (Maybe Tp, Maybe Tp)
getSubstitutedTypes info = 
   do let (t1,t2) = getTwoTypes info
      mt1 <- safeApplySubst t1
      mt2 <- safeApplySubst t2
      return (mt1, mt2)
