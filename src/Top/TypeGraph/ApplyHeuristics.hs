-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.ApplyHeuristics (applyHeuristics, expandPath, predicatePath) where

import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Heuristics
import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
import Utils (internalError)
import Control.Monad
import Data.List
import Top.Types	
import Data.Maybe
import qualified Data.Set as S
import Data.FiniteMap
import Graph (topSort)
import Top.States.BasicState (printMessage)
import Top.States.TIState
import Debug.Trace

applyHeuristics :: HasTypeGraph m info => [Heuristic info] -> m ([EdgeId], [info])
applyHeuristics heuristics =
   let rec thePath = 
          case simplifyPath thePath of
             Empty -> internalError "Top.TypeGraph.ApplyHeuristics" "applyHeuristics" "unexpected empty path"
             Fail  -> return ([],[])
             path  ->
                do (action, edgeId1, info1) <- evalHeuristics path heuristics
                   action
                   let restPath = changeStep (\t@(a,_,_) -> if a `elem` edgeId1 then Fail else Step t) path
                   (edgeId2, info2) <- rec restPath
                   return (edgeId1++edgeId2, info1++info2)
   in 
      do errorPath <- allErrorPaths
         rec (removeSomeDuplicates info3ToEdgeNr errorPath)
 
evalHeuristics :: HasTypeGraph m info => Path (EdgeId, EdgeNr, info) -> [Heuristic info] -> m (m (), [EdgeId], [info])
evalHeuristics path heuristics = 
   rec edgesBegin heuristics
   
 where
   edgesBegin = nubBy eqInfo3 (steps path)
   
   rec edges [] = 
      case edges of
         (edgeId, cNR, info) : _ -> 
            do printMessage ("\n*** The selected constraint: " ++ show cNR ++ " ***\n")
               return (return (), [edgeId], [info])
         _ -> internalError "Top.TypeGraph.ApplyHeuristics" "evalHeuristics" "empty list"
             
   rec edges (Heuristic heuristic:rest) = 
      case heuristic of
          
         Filter name f -> 
            do edges' <- f edges                
               printMessage (name ++ " (filter)")
               printMessage ("   " ++ showSet (map (\(_,i,_) -> i) edges'))
               rec edges' rest
               
         PathComponent f -> 
            rec edges (f path : rest)  
            
         Voting selectors -> 
            do printMessage ("Voting with "++show (length selectors) ++ " heuristics")
               maybeResult <- 
                  let noAction f x = 
                         do mTuple <- f x
                            case mTuple of
                               Nothing -> return Nothing
                               Just (a,b,c,d) -> return (Just (return (),a,b,c,d))
                            
                      getResults (Selector (name, f)) =
                         do printMessage ("- "++name++" (selector)")
                            mapM (noAction f) edges  
				      
                      getResults (SelectorList (name, f)) =
                         do printMessage ("- "++name++" (list selector)")
                            result <- noAction f edges
                            return [result]
				      
                      getResults (SelectorAction (name, f)) = 
                         do printMessage ("- "++name++" (action selector)")
                            mapM f edges
                            
                      getResults (SelectorPath f) =
                         getResults (f path)                    
		   
                      op best selector = 
                         do results <- getResults selector
                            case catMaybes results of
                               [] -> return best
                               rs -> do let f (_,i,s,es,_) = "    "++s++" (prio="++show i++") => "++showSet es
                                        printMessage (foldr1 (\x y -> x++"\n"++y) (map f rs))
                                        let best' = maximumBy (\(_,i1,_,_,_) (_,i2,_,_,_) -> i1 `compare` i2) rs
                                            (_,score,_,_,_) = best'
                                        case best of
                                           Just (_,i,_,_,_) | i >= score -> return best
                                           _ -> return (Just best')                                           
                  in foldM op Nothing selectors
                  
               case maybeResult of                           
                  Nothing -> 
                     do printMessage "Unfortunately, none of the heuristics could be applied"
                        rec edges rest
                  Just (action,prio, _, edgeIds, infos) ->
                     do printMessage ("\n*** With priority "++show prio++", "++showSet edgeIds++" was selected\n")
                        return (action, edgeIds, infos)
              
showSet :: Show a => [a] -> String
showSet as = "{" ++ f (map show as) ++ "}"
   where f [] = ""
         f xs = foldr1 (\x y -> x++","++y)  (map show xs)

maxPathSize :: Integer
maxPathSize = 1

allErrorPaths :: HasTypeGraph m info => m (Path (EdgeId, EdgeNr, info))
allErrorPaths = 
   do is      <- getMarkedPossibleErrors     
      cGraph  <- childrenGraph is     
      let toCheck = nub $ concat (is : [ [a,b] | ((a,b),_) <- cGraph ])
      paths1  <- constantClashPaths toCheck
      paths2  <- infiniteTypePaths cGraph  
      let errorPath = reduceNumberOfPaths (simplifyPath (altList (paths1 ++ paths2)))                   
      expandPath errorPath    
      
----------------------------

-- not simplified: can also contain implied edges
constantClashPaths :: HasTypeGraph m info => [VertexId] -> m [TypeGraphPath info]
constantClashPaths []     = return []
constantClashPaths (first:rest) = 
   do vertices <- verticesInGroupOf first
      let vs    = map fst vertices
          rest' = filter (`notElem` vs) rest
      pathInGroup vertices <++> constantClashPaths rest'     

 where
  pathInGroup :: HasTypeGraph m info => [(VertexId, VertexInfo)] -> m [TypeGraphPath info]
  pathInGroup = errorPath . groupTheConstants . getConstants
   
  getConstants :: [(VertexId, VertexInfo)] -> [(VertexId, String)]
  getConstants vertices = 
     [ (i, s  ) | (i, (VCon s  , _)) <- vertices ] ++
     [ (i, "@") | (i, (VApp _ _, _)) <- vertices ]
     
  -- lists of vertex numbers with the same type constant
  -- (all vertices are in the same equivalence group)
  groupTheConstants :: [(VertexId, String)] -> [[VertexId]]
  groupTheConstants =  
     sortBy (\xs ys -> length xs `compare` length ys)
     .  map (map fst)
     .  groupBy (\x y -> snd x    ==     snd y)
     .  sortBy  (\x y -> snd x `compare` snd y)
   
  errorPath :: HasTypeGraph m info => [[VertexId]] -> m [TypeGraphPath info]   
  errorPath []        = return []             
  errorPath [_]       = return []
  errorPath (is:iss) = 
     let f i = allPathsList i (concat iss)
     in mapM f is <++> errorPath iss
     
----------------------------     

-- not simplified: can also contain implied edges
infiniteTypePaths :: HasTypeGraph m info => ChildGraph -> m [TypeGraphPath info]
infiniteTypePaths cGraph =        
   do pss <- mapM (makePathForInfiniteGroup . inThisGroup) allGroups
      return (concat pss)
      -- error (unlines $ map (show . inThisGroup) allGroups)
       
 where        
   allGroups :: [[VertexId]]
   allGroups = infiniteGroups (map fst cGraph)
   
   -- puts the eqgroup with the least childedges to another group in front of the list 
   inThisGroup :: [VertexId] -> ChildGraph
   inThisGroup infGroup =
      let p ((x, y), _) = (x `elem` infGroup) && (y `elem` infGroup)
          f (_, xs) (_, ys) = length xs `compare` length ys
      in sortBy f (filter p cGraph)
                
   makePathForInfiniteGroup :: HasTypeGraph m info => ChildGraph -> m [TypeGraphPath info]
   makePathForInfiniteGroup groupGraph =
      case groupGraph of
         [] -> return []
         (_, childEdges) : rest ->
            let g (x, y) = allSubPathsList (concatMap snd rest) y [x]
            in mapM g childEdges <++> infiniteTypePaths rest 

type ChildGraph = [((VertexId, VertexId), [(VertexId, VertexId)])]
      
childrenGraph :: HasTypeGraph m info => [VertexId] -> m ChildGraph
childrenGraph = rec [] 
   where 
      rec as []     = return as
      rec as (i:is) = 
         do vertices <- verticesInGroupOf i
            ri       <- representativeInGroupOf i           
            if ri `elem` (map (fst . fst) as)
              then rec as is
              else do let cs = concat [ [(n, l), (n, r)] | (n, (VApp l r, _)) <- vertices ]
                      cs' <- let f t = do r <- representativeInGroupOf (snd t)
                                          return (r, t)
                             in mapM f cs
                      let children = map (\((a,b):xs) -> (a,b:map snd xs))
                                   . groupBy (\x y -> fst x     ==    fst y)
                                   . sortBy  (\x y -> fst x `compare` fst y)
                                   $ cs'
                      rec ([ ((ri, rc), xs) | (rc, xs) <- children ] ++ as) (map fst children ++ is)      

infiniteGroups :: [(VertexId, VertexId)] -> [[VertexId]]
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

allSubPathsList :: HasTypeGraph m info => [(VertexId, VertexId)] -> VertexId -> [VertexId] -> m (TypeGraphPath info) 
allSubPathsList childList vertex targets = rec S.emptySet vertex
 where
   rec :: HasTypeGraph m info => S.Set VertexId -> VertexId -> m (TypeGraphPath info)
   rec without start =  
      do vs <- verticesInGroupOf start
         case any (`elem` map fst vs) targets of 
	 
            True  -> -- targets are in the same group as the source
               do directPath <- allPathsListWithout without start targets
                  return (simplifyPath directPath)
	       
            False -> -- go down to another equivalence group  
               let recDown (newStart, childTargets) =
                      do let newWithout = without `S.union` S.mkSet (map fst vs){- don't return to this equivalence group -}
                             f ct = let set = S.mkSet [ t | t <- childTargets, t /= ct ]
                                    in rec (set `S.union` newWithout) ct
                         path     <- allPathsListWithout without start [newStart]
                         newPaths <- mapM f childTargets
                         return (path :+: altList newPaths)
                   
                   targetPairs :: [(VertexId, [VertexId])]
                   targetPairs =
                      let p (i, j) =  i `elem` map fst vs
			                       && not (i `S.elementOf` without || j `S.elementOf` without)
                      in map (\((i,j):rest) -> (i, j:map snd rest))
                       . groupBy (\x y -> fst x     ==    fst y)
                       . sortBy  (\x y -> fst x `compare` fst y)
                       $ filter p childList
               in
                  do extendedPaths <- mapM recDown targetPairs
                     return (altList extendedPaths)           
	           
expandPath :: HasTypeGraph m info => TypeGraphPath info -> m (Path (EdgeId, EdgeNr, info))
expandPath Fail = return Fail
expandPath path =
   let impliedEdges = nub [ intPair (v1, v2) | (_, Implied _ (VertexId v1) (VertexId v2)) <- steps path ]
   in do expandTable <- impliedEdgeTable impliedEdges
         let 
             convert history path = 
                case path of 
                   Empty -> Empty
                   Fail  -> Fail
                   p1 :+: p2 -> convert history p1 :+: convert history p2
                   p1 :|: p2 -> convert history p1 :|: convert history p2
                   Step (edge, edgeInfo) -> 
                      case edgeInfo of
                         Initial cnr info -> Step (edge, cnr, info)
                         Child _ -> Empty
                         Implied _ (VertexId v1) (VertexId v2)
                            | pair `S.elementOf` history ->
                                 Empty
                            | otherwise -> 
                                 convert (S.addToSet history pair) (lookupPair expandTable pair)
                          where 
                           pair = intPair (v1, v2)

         return (convert S.emptySet path)                 

impliedEdgeTable :: HasTypeGraph m info => [IntPair] -> m (PathMap info)
impliedEdgeTable = insertPairs emptyFM
 where
   insertPairs fm [] = return fm
   insertPairs fm (pair:rest)
      | pair `elemFM` fm = insertPairs fm rest
      | otherwise =
           do path <- let (i1, i2) = tupleFromIntPair pair
                      in allPaths (VertexId i1) (VertexId i2)
              let new = nub [ intPair (v1, v2) | (_, Implied _ (VertexId v1) (VertexId v2)) <- steps path ]
              insertPairs (addToFM fm pair path) (rest `union` new)
	  
-------------------------------
-- 

newtype IntPair = Hidden_IP { tupleFromIntPair :: (Int, Int) }

intPair :: (Int, Int) -> IntPair
intPair (x, y)
   | x <= y    = Hidden_IP (x, y)
   | otherwise = Hidden_IP (y, x)
 
instance Show IntPair where
   show (Hidden_IP pair) = show pair
   
instance Eq IntPair where
   Hidden_IP pair1 == Hidden_IP pair2 = 
      pair1 == pair2

instance Ord IntPair where
   Hidden_IP pair1 `compare` Hidden_IP pair2 = 
      pair1 `compare` pair2

type PathMap info = FiniteMap IntPair (Path (EdgeId, PathStep info))

lookupPair :: PathMap info -> IntPair -> Path (EdgeId, PathStep info)
lookupPair fm pair = 
   let err = internalError "Top.TypeGraph.ApplyHeuristics" "lookupPair" "could not find implied edge while expanding"
   in lookupWithDefaultFM fm err pair

-- move to another module
predicatePath :: HasTypeGraph m info => m (Path (EdgeId, PathStep info))
predicatePath =
   do ps       <- getPredicates
      simples  <- simplePredicates ps
      makeList (S.emptySet) Empty simples

 where 
  simplePredicates ps =
     do classEnv <- getClassEnvironment
        syns     <- getTypeSynonyms
        let reduced = fst (contextReduction syns classEnv ps)
        return [ (s, VertexId i) | Predicate s (TVar i) <- reduced ]
     
  makeList history path pairs = 
     do xs <- mapM (make history path) pairs
        return (altList xs)
       
  make history path (pClass, i)
     | i `S.elementOf` history = return Fail
     | otherwise = 
          do classEnv <- getClassEnvironment
             syns     <- getTypeSynonyms
             vertices <- verticesInGroupOf i
             
             -- vertices to inspect
             let constants  = [ (vid, TCon s) | (vid, (VCon s, _)) <- vertices ]
             applys <- let f i' = do tp <- typeFromTermGraph i'
                                     return (i', tp)
                       in mapM f [ i' | (i', (VApp _ _, _)) <- vertices ]
                           
             let f (vid, tp)
                    | null errs = -- everything is okay: recursive call
                         do let -- don't visit these vertices
                                donts = S.mkSet [ VertexId i | i <- ftv (map snd applys), i `notElem` ftv tp ]
                            path'   <- allPathsListWithout history i [vid]
                            simples <- simplePredicates reduced
                            makeList (donts `S.union` newHistory) (path :+: path') simples
                               
                    | otherwise = -- this is an error path
                         do path' <- allPathsListWithout history i [vid]
                            return (path :+: path')
                               
                  where (reduced, errs) = contextReduction syns classEnv [Predicate pClass tp]
                        newHistory      = S.mkSet (map fst vertices) `S.union` history
                        
             xs <- mapM f (constants ++ applys)
             return (altList xs)