-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.ApplyHeuristics (applyHeuristics) where

import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Heuristics
import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
import Utils (internalError)
import Control.Monad
import Data.List
import Top.Types	
import Data.Maybe
import Data.FiniteMap
import Graph (topSort)
import Top.States.BasicState (printMessage)

applyHeuristics :: HasTypeGraph m info => [Heuristic info] -> m ([EdgeID], [info])
applyHeuristics heuristics =
   let rec thePath = 
          case simplifyPath thePath of
             Empty -> internalError "Top.TypeGraph.ApplyHeuristics" "applyHeuristics" "unexpected empty path"
             Fail  -> return ([],[])
             path  ->
                do (edgeID1, info1) <- evalHeuristics path heuristics
                   let restPath = changeStep (\t@(a,_,_) -> if a `elem` edgeID1 then Fail else Step t) path
                   (edgeID2, info2) <- rec restPath
                   return (edgeID1++edgeID2, info1++info2)
   in 
      do (errorPath, errorGroups) <- allErrorPaths         
         rec (removeSomeDuplicates eqInfo3 errorPath)   

evalHeuristics :: HasTypeGraph m info => Path (EdgeID, Int, info) -> [Heuristic info] -> m ([EdgeID], [info])
evalHeuristics path heuristics = 
   let 
       edgesBegin = nubBy eqInfo3 (steps path)
       
       rec edges [] = 
          case edges of
             (edgeID, cNR, info):_ -> do printMessage ("\n*** The selected constraint: " ++ show cNR ++ " ***\n")
                                         return ([edgeID], [info])
             _                     -> internalError "Top.TypeGraph.ApplyHeuristics" "evalHeuristics" "empty list"
             
       rec edges (Heuristic heuristic:rest) = 
          case heuristic of
          
             Filter name f -> 
                do edges' <- f edges                
                   printMessage (name ++ " (filter)")
                   printMessage ("   " ++ showSet (map (\(_,i,_) -> i) edges'))
                   rec edges' rest
             
             Voting selectors -> 
                do printMessage ("Voting with "++show (length selectors) ++ " heuristics")
                   mres <- let op best (Selector (name, f)) = 
                                  do printMessage ("- "++name++" (selector)")
                                     results <- mapM f edges                                     
                                     case catMaybes results of
                                        [] -> return best
                                        rs -> do let f (i,s,es,_) = "    "++s++" (prio="++show i++") => "++showSet es
                                                 printMessage (foldr1 (\x y -> x++"\n"++y) (map f rs))
                                                 let best' = maximumBy (\(i1,_,_,_) (i2,_,_,_) -> i1 `compare` i2) rs
                                                     (score,_,_,_) = best'
                                                 case best of
                                                    Just (i,_,_,_) | i >= score -> return best
                                                    _ -> return (Just best')
                                                    
                           in foldM op Nothing selectors
                   case mres of                           
                      Nothing -> 
                         do printMessage "Unfortunately, none of the heuristics could be applied"
                            rec edges rest
                      Just (prio, _, edgeIDs, infos) ->
                         do printMessage ("\n*** With priority "++show prio++", "++showSet edgeIDs++" was selected\n")
                            return (edgeIDs, infos)
                
                {-
             Selector name f ->         
                do results <- mapM f edges
                   case catMaybes results of
                      (:ts -> 
                         do printMessage (name ++ "(selector)")
                            printMessage ("   " ++ showSet (map fst (t:ts)))
                            return t
                      _   -> 
                         do printMessage (name ++ "(selector): failed")
                            rec edges rest -}

             PathComponent f -> 
                rec edges (f path : rest)

             Skip ->                
                rec edges rest
                
   in rec edgesBegin heuristics

showSet :: Show a => [a] -> String
showSet as = "{" ++ f (map show as) ++ "}"
   where f [] = ""
         f xs = foldr1 (\x y -> x++","++y)  (map show xs)
      
allErrorPaths :: HasTypeGraph m info => m (Path (EdgeID, Int, info), [Int])
allErrorPaths = 
   do 
      is      <- extractPossibleErrors      
      cGraph  <- childrenGraph is     
      let toCheck = nub $ concat (is : [ [a,b] | ((a,b),_) <- cGraph ])
      paths1  <- constantClashPaths toCheck                                    
      paths2  <- infiniteTypePaths cGraph        
      let errorPath = simplifyPath . altList $ map snd (paths1 ++ paths2)                          
      total <- expandPath errorPath 
      return (total, nub (concatMap fst (paths1 ++ paths2)))
      
                                         
----------------------------

-- not simplified: can also contain implied edges
constantClashPaths :: HasTypeGraph m info => [VertexID] -> m [([Int], Path (EdgeID, EdgeInfo info))]
constantClashPaths []     = return []
constantClashPaths (i:is) = 
   do vertices <- verticesInGroupOf i   
      repr     <- representativeInGroupOf i   
      paths1   <- pathInGroup vertices         
      paths2   <- let vs = map fst vertices
                  in constantClashPaths (filter (`notElem` vs) is)
      return $ [([repr], path) | path <- paths1] ++ paths2

 where 
  pathInGroup vertices = 
     let -- lists of vertex numbers with the same type constant
         -- (all vertices are in the same equivalence group)
         vList :: [[VertexID]]
         vList =  sortBy (\xs ys -> length xs `compare` length ys)
               .  map (map fst)
               .  groupBy (\x y -> snd x    ==     snd y)
               .  sortBy  (\x y -> snd x `compare` snd y)
               $  [ (i, s  ) | (i, (VCon s  , _)) <- vertices ] 
               ++ [ (i, "@") | (i, (VApp _ _, _)) <- vertices ]
            
         errorPath []        = return []             
         errorPath [_]       = return []
         errorPath (is:rest) = do paths1 <- mapM (\i -> allPathsList i (concat rest)) is
                                  paths2 <- errorPath rest
                                  return (paths1 ++ paths2)
     in errorPath vList
     
----------------------------     

-- not simplified: can also contain implied edges
infiniteTypePaths :: HasTypeGraph m info => ChildGraph -> m [([Int], Path (EdgeID, EdgeInfo info))]
infiniteTypePaths = rec

  where   
     rec cGraph =       
        let iGroups = infiniteGroups (map fst cGraph)
        in do pss <- mapM (rec1 cGraph) iGroups
              return (concat pss)
        
     rec1 cGraph iGroup 
      | null cGraph = return []
      | otherwise   = 
      
        let groupGraph@((_,childEdges):rest) = sortBy (\x y -> length (snd x) `compare` length (snd y))
                                                $ [ tuple | tuple@((x, y), _) <- cGraph, x `elem` iGroup, y `elem` iGroup ]
            groupChildList = concatMap snd groupGraph                                              
        in do paths1 <- mapM (\(x,y) -> allSubPathsList groupChildList y [x]) childEdges              
              paths2 <- rec rest
              return $ (iGroup, altList paths1) :  paths2

type ChildGraph = [((VertexID, VertexID), [(VertexID, VertexID)])]
      
childrenGraph :: HasTypeGraph m info => [VertexID] -> m ChildGraph
childrenGraph = rec [] 
   where 
      rec as []     = return as
      rec as (i:is) = 
         do vertices <- verticesInGroupOf i
            ri       <- representativeInGroupOf i           
            if ri `elem` (map (fst . fst) as)
              then rec as is
              else do let cs = concat [ [(i, l), (i, r)] | (i, (VApp l r, _)) <- vertices ]
                      cs' <- let f t = do r <- representativeInGroupOf (snd t)
                                          return (r, t)
                             in mapM f cs
                      let children = map (\((a,b):xs) -> (a,b:map snd xs))
                                   . groupBy (\x y -> fst x     ==    fst y)
                                   . sortBy  (\x y -> fst x `compare` fst y)
                                   $ cs'
                      rec ([ ((ri, rc), xs) | (rc, xs) <- children ] ++ as) (map fst children ++ is)      

infiniteGroups :: [(VertexID, VertexID)] -> [[VertexID]]
infiniteGroups xs = 
   let representatives = nub (map fst xs ++ map snd xs)
       map1 = listToFM (zip representatives [0..])
       f1   = lookupWithDefaultFM map1 (internalError "Top.TypeGraph.ApplyHeuristics" "infiniteGroups" "error in lookup1 of makeMap")
       map2 = listToFM (zip [0..] representatives)
       f2   = lookupWithDefaultFM map2 (internalError "Top.TypeGraph.ApplyHeuristics" "infiniteGroups" "error in lookup2 of makeMap")
       edgeList = [ (f1 i, f1 c) | (i, c) <- xs ]
       groups   = topSort (length representatives - 1) edgeList
       selfRecursive = [ f1 i | (i, j) <- xs, i == j ]
       recursive = let p [i] = i `elem` selfRecursive
                       p is  = length is > 1
                   in map (map f2) ((filter p groups))
   in recursive

allSubPathsList :: HasTypeGraph m info => [(VertexID, VertexID)] -> VertexID -> [VertexID] -> m (Path (EdgeID, EdgeInfo info))   
allSubPathsList childList start targets = rec [] start 
   where
      rec :: HasTypeGraph m info => [VertexID] -> VertexID -> m (Path (EdgeID, EdgeInfo info))
      rec without' start = 
         do vs <- verticesInGroupOf start
            let without = without' `union` [ i | (i, (VCon _, _)) <- vs]
            directPath <- allPathsListWithout without start targets
            let simplifiedDirect = simplifyPath directPath
              
                successors = 
                   let rec i = i : [ s | (i',j) <- childList, i == i', s <- rec j ]              
                   in nub . rec
            
                recWithout without path =  union without 
                                        $ nub . concat 
                                        $ map successors
                                        $ [ n1 | (EdgeID n1 n2,_) <- steps path ]
                   
                recExtendPath without path = 
                   case path of
                      Fail      -> return Fail
                      p1 :+: p2 -> do p2' <- recExtendPath (recWithout without p1) p2
                                      return (p1 :+: p2')
                      p1 :|: p2 -> do p1' <- recExtendPath without p1
                                      p2' <- recExtendPath without p2
                                      return (p1' :|: p2')                      
                      Empty     -> 
                         do let childTargets = [ j | (i,j) <- childList, i == start, j `notElem` without]
                            newPaths <- let f ct = do path <- rec (start : (childTargets \\ [ct]) ++ without) ct
                                                      return (  {- Step (EdgeID start ct, Child 13) 
                                                            :+: -} path 
                                                             )
                                        in mapM f childTargets
                            return (altList newPaths)      
                      Step (EdgeID n1 n2,_) ->
                         do let childTargets = [ j | (i,j) <- childList, i == n2, j `notElem` without ]
                            newPaths <- let f ct = do path <- rec ((n2:successors n1) `union` without) ct
                                                      return (  {- Step (EdgeID n2 ct, Child 13) 
                                                            :+: -} path 
                                                             )
                                        in mapM f childTargets
                            return (path :+: altList newPaths)
            
            case simplifiedDirect of   
            
               Fail -> do childPath  <- let newTargets = nub (map fst childList) \\ (without ++ targets)                               
                                        in allPathsListWithout without start newTargets                                           
                          childPathExtended <- recExtendPath without childPath            
                          return childPathExtended
                          
               _    -> return simplifiedDirect               
            
      
expandPath :: HasTypeGraph m info => Path (EdgeID, EdgeInfo info) -> m (Path (EdgeID, Int, info))
expandPath path =
   do expandTable  <- makeTable (implied path) emptyFM
      expandedPath <- rec [] expandTable path           
      return (simplifyPath expandedPath)
         
 where   
    implied :: Path (EdgeID, EdgeInfo info) -> [(VertexID,VertexID)] 
    implied path = [ (v1, v2) | (_, Implied _ v1 v2) <- steps path ]
 
    makeTable :: HasTypeGraph m info => 
                    [(VertexID,VertexID)] 
                       ->    FiniteMap (VertexID,VertexID) (Path (EdgeID, EdgeInfo info)) 
                       -> m (FiniteMap (VertexID,VertexID) (Path (EdgeID, EdgeInfo info)))
    makeTable [] fm = return fm
    makeTable (pair@(v1, v2):rest) fm
       | elemFM pair fm = makeTable rest fm
       | otherwise =
            do path <- allPathsList v1 [v2]  
               makeTable (implied path ++ rest) (addToFM fm pair path)
           
    rec history fm p = 
       let f (edgeID, edgeInfo) = 
              case edgeInfo of
                 Initial cnr info -> 
                    return (Step (edgeID, cnr, info))
                 Child _ ->
                    return Empty
                 Implied _ v1 v2
                    | pair `elem` history -> 
                         return Empty
                    | otherwise -> 
                         rec (pair:history) fm ep
                       where pair = (v1, v2)
                             err  = internalError "Top.TypeGraph.ApplyHeuristics" "expandPath" "could not find implied edge while expanding"
                             ep   = lookupWithDefaultFM fm err pair
       in changeStepM f p
