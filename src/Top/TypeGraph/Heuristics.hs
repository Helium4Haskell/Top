-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.Heuristics where

import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
import Top.States.BasicState
import Top.Types
import Control.Monad
import Utils (internalError)

-----------------------------------------------------------------------------

newtype Heuristic  info = Heuristic (forall m . HasTypeGraph m info => HComponent m info)
newtype HasTypeGraph m info => Selector m info = Selector  (String, (EdgeID, Int, info) -> m (Maybe (Int, String, [EdgeID], [info])))

data HComponent m info 
     = Filter    String ([(EdgeID, Int, info)] -> m [(EdgeID, Int, info)])
     | Voting   [Selector m info]
     | PathComponent (Path (EdgeID, Int, info) -> Heuristic info)
     | Skip
          
resultsEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((EdgeID,Int,info) -> m a) -> HComponent m info
resultsEdgeFilter selector description function =
   Filter description $ \edges -> 
   do tupledList <- let f tuple = 
                           do result <- function tuple
                              return (result, tuple)
                    in mapM f edges
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
   Filter description $ \edges -> 
      filterM function edges

-----------------------------------------------------------------------------
     
doWithoutEdge :: HasTypeGraph m info => (EdgeID,info) -> m result -> m result
doWithoutEdge (edge@(EdgeID v1 v2),info) computation =
   do deleteEdge edge       
      result <- computation           
      addEdge edge info
      return result
                   
-- keep a history to avoid non-termination (for type-graphs that contain an infinite type)
safeApplySubst :: HasTypeGraph m info => Tp -> m (Maybe Tp)
safeApplySubst = rec [] where 

  rec history tp = case tp of 
  
    TVar i | i `elem` history 
               -> return Nothing
           | otherwise 
               -> do vertices  <- verticesInGroupOf  i
                     constants <- constantsInGroupOf i
                     children  <- childrenInGroupOf  i                     
                     case constants of 
                        [s] -> return (Just (TCon s))               
                        []  -> case children of 
                                  []        -> let rep = fst (head vertices)
                                               in return (Just (TVar rep))
                                  (_, (c1, c2)):_ -> 
                                     do mt1 <- rec (i : history) (TVar c1)
                                        mt2 <- rec (i : history) (TVar c2)
                                        return $ 
                                           do tp1 <- mt1
                                              tp2 <- mt2
                                              return (TApp tp1 tp2)
                        _ -> return Nothing
    TCon s     -> return (Just tp)
    
    TApp t1 t2 -> do mt1 <- rec history t1
                     mt2 <- rec history t2
                     case (mt1,mt2) of 
                       (Just t1',Just t2') -> return (Just $ TApp t1' t2')
                       _                   -> return Nothing

eqInfo3 :: (EdgeID, Int, info) -> (EdgeID, Int, info) -> Bool
eqInfo3 (a1,b1,_) (a2,b2,_) = b1 == b2 -- && a1 == a2

class HasTwoTypes a where
   getTwoTypes :: a -> (Tp, Tp)

getSubstitutedTypes :: (HasTypeGraph m info, HasTwoTypes info) => info -> m (Maybe Tp, Maybe Tp)
getSubstitutedTypes info = 
   do let (t1,t2) = getTwoTypes info
      mt1 <- safeApplySubst t1
      mt2 <- safeApplySubst t2
      return (mt1, mt2)
