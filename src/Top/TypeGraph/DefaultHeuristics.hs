-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.DefaultHeuristics where

import Top.TypeGraph.Basics
import Top.TypeGraph.Heuristics 
import Top.TypeGraph.Paths 
import Data.List
import Data.FiniteMap
import Top.States.BasicState

-----------------------------------------------------------------------------

defaultHeuristics :: Show info => [Heuristic info]
defaultHeuristics = 
   [ highParticipation 1.00, positionInList ]
         
-----------------------------------------------------------------------------

-- compute the smallest 'minimal' sets. This computation is very(!) costly
--   (might take a long time for complex inconsistencies)
inMininalSet :: Heuristic info
inMininalSet = 
   Heuristic (
      PathComponent (\path -> 
         let sets = minimalSets eqInfo3 path
             candidates = nubBy eqInfo3 (concat sets)
         in Heuristic (edgeFilter "In a smallest minimal set"
               (\e -> return (any (eqInfo3 e) candidates)))))

-- although not as precise as the minimal set analysis, this calculates the participation of
-- each edge in all error paths. 
-- Default ratio = 1.0  (100 percent)
--   (the ratio determines which scores compared to the best are accepted)
highParticipation :: Show info => Double -> Heuristic info
highParticipation ratio = 
   Heuristic (
      PathComponent (\path -> 
         let (nrOfPaths, fm) = participationMap (mapPath (\(_,cnr,_) -> cnr) path)
             participationList = fmToList fm
             maxInList = maximum (map snd participationList)
             limit     = round (fromIntegral maxInList * ratio) `max` 1
             goodCNrs  = [ cnr | (cnr, i) <- participationList, i >= limit ]
  
             -- prints a nice report
             msg es = unlines (title : replicate 50 '-' : map f es)
             title  = "cnr edge      ratio   info"
             f (edgeID,cnr,info) = 
                take 4  (show cnr++(if cnr `elem` goodCNrs then "*" else "")++repeat ' ') ++
                take 10 (show edgeID++repeat ' ') ++
                take 8  (show (lookupWithDefaultFM fm 0 cnr * 100 `div` nrOfPaths)++"%"++repeat ' ') ++
                "{"++show info++"}"
                
         in Heuristic (Filter ("Participation ratio [ratio="++show ratio++"]")
               (\es -> do printMessage (msg es)
                          return (filter (\(_,cnr,_) -> cnr `elem` goodCNrs) es)))))

positionInList :: Heuristic info
positionInList = 
   Heuristic ( 
      let f (edge@(EdgeID v1 v2), cnr, info) = return cnr
      in maximalEdgeFilter "Constraint number of edge" f)
