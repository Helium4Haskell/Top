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
import Top.TypeGraph.ApplyHeuristics

-----------------------------------------------------------------------------

defaultHeuristics :: Show info => [Heuristic info]
defaultHeuristics = 
   [ highParticipation 1.00, positionInList ]
         
-----------------------------------------------------------------------------

-- |Compute the smallest 'minimal' sets. This computation is very(!) costly
--   (might take a long time for complex inconsistencies)
inMininalSet :: Heuristic info
inMininalSet = 
   Heuristic (
      PathComponent (\path -> 
         let sets = minimalSets eqInfo3 path
             candidates = nubBy eqInfo3 (concat sets)
         in Heuristic (edgeFilter "In a smallest minimal set"
               (\e -> return (any (eqInfo3 e) candidates)))))

-- |Although not as precise as the minimal set analysis, this calculates the participation of
-- each edge in all error paths. 
-- Default ratio = 1.0  (100 percent)
--   (the ratio determines which scores compared to the best are accepted)
highParticipation :: Show info => Double -> Heuristic info
highParticipation ratio = 
   Heuristic (
      PathComponent (\path -> 
         Heuristic (Filter ("Participation ratio [ratio="++show ratio++"]")
                   (selectTheBest path))))
 where
   selectTheBest path es = 
      let (nrOfPaths, fm)   = participationMap (mapPath (\(_,cnr,_) -> cnr) path)
          participationList = fmToList (filterFM p fm)
          p cnr _    = cnr `elem` activeCNrs
          activeCNrs = [ cnr | (_, cnr, _) <- es ] 
          maxInList  = maximum (map snd participationList)
          limit     -- test if one edge can solve it completely
             | maxInList == nrOfPaths = maxInList 
             | otherwise              = round (fromIntegral maxInList * ratio) `max` 1
          goodCNrs   = [ cnr | (cnr, i) <- participationList, i >= limit ]
          bestEdges  = filter (\(_,cnr,_) -> cnr `elem` goodCNrs) es
  
          -- prints a nice report
          msg    = unlines ("" : title : replicate 50 '-' : map f es)
          title  = "cnr edge      ratio   info"
          f (edgeID,cnr,info) = 
             take 4  (show cnr++(if cnr `elem` goodCNrs then "*" else "")++repeat ' ') ++
             take 10 (show edgeID++repeat ' ') ++
             take 8  (show (lookupWithDefaultFM fm 0 cnr * 100 `div` nrOfPaths)++"%"++repeat ' ') ++
             "{"++show info++"}"
      in do printMessage msg
            return bestEdges
            
-- |Select the "latest" constraint
positionInList :: Heuristic info
positionInList = 
   Heuristic ( 
      let f (_, cnr, _) = return cnr
      in maximalEdgeFilter "Constraint number of edge" f)

-- |Select only specific constraint numbers
selectConstraintNumbers :: [EdgeNr] -> Heuristic info
selectConstraintNumbers is =
   Heuristic (
      let f (_, cnr, _) = return (cnr `elem` is)
      in edgeFilter ("select constraint numbers " ++ show is) f)

-- |Select only the constraints for which there is evidence in the predicates
-- of the current state that the constraint at hand is incorrect.
inPredicatePath :: Heuristic info
inPredicatePath = 
   Heuristic (Filter "in a predicate path" f) where

    f xs = 
       do pp  <- predicatePath
          path <- expandPath (simplifyPath pp) 
          let cnrs = nub [ c | (_, c, _) <- steps path ]
              p (_, cnr, _) = cnr `elem` cnrs
              ys = filter p xs
          return (if null ys then xs else ys)