-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.Paths where  

import Data.List
import Data.Maybe
import Data.FiniteMap

----------------------
   
data Path a = Path a :|: Path a   -- alternative   
            | Path a :+: Path a   -- sequence
            | Step a
            | Fail
            | Empty                   

seqList, seqList1 :: [Path a] -> Path a
seqList  = foldr  (:+:) Empty
seqList1 = foldr1 (:+:)

altList, altList1 :: [Path a] -> Path a
altList  = foldr  (:|:) Fail
altList1 = foldr1 (:|:)  

instance Show a => Show (Path a) where
   show path = 
      case path of
         x :|: y -> show x ++ "|" ++ show y
         x :+: y -> parIf (pathPrio x < 1) (show x) ++ "+" ++ parIf (pathPrio y < 1) (show y)
         Step a  -> show a
         Fail    -> "Fail"
         Empty   -> "Empty"

    where pathPrio :: Path a -> Int
          pathPrio (x :|: y) = 0
          pathPrio (x :+: y) = 1
          pathPrio _         = 2
          
          parIf b s = if b then "("++s++")" else s
      
steps :: Path a -> [a]
steps path = 
   case path of 
      x :|: y -> steps x ++ steps y
      x :+: y -> steps x ++ steps y
      Step a  -> [a]
      Fail    -> []
      Empty   -> []

mapPath :: (a -> b) -> Path a -> Path b
mapPath f = changeStep (Step . f) 

changeStep :: (a -> Path b) -> Path a -> Path b
changeStep f path = 
   case path of
      x :|: y -> changeStep f x :|: changeStep f y
      x :+: y -> changeStep f x :+: changeStep f y
      Step a  -> f a
      Fail    -> Fail
      Empty   -> Empty  
      
changeStepM :: Monad m => (a -> m (Path b)) -> Path a -> m (Path b)
changeStepM f path = 
   case path of
      x :|: y -> do x' <- changeStepM f x; y' <- changeStepM f y; return (x' :|: y')
      x :+: y -> do x' <- changeStepM f x; y' <- changeStepM f y; return (x' :+: y')
      Step a  -> f a
      Fail    -> return Fail
      Empty   -> return Empty          
             
minCompleteInPath :: (a -> a -> Ordering) -> Path a -> Maybe a
minCompleteInPath f = rec . simplifyPath
   where 
      rec path = 
         case path of
            x :|: y -> do v1 <- rec x; v2 <- rec y; return (minimumBy f [v1, v2])
            x :+: y -> do v1 <- rec x; v2 <- rec y; return (maximumBy f [v1, v2])
            Step a  -> Just a
            Fail    -> Nothing
            Empty   -> Nothing

simplifyPath :: Path a -> Path a      
simplifyPath path =
   case path of  
      x :|: y -> case (simplifyPath x, simplifyPath y) of
                    (Empty, _) -> Empty
                    (_, Empty) -> Empty
                    (Fail, p2) -> p2
                    (p1, Fail) -> p1
                    (p1, p2)   -> p1 :|: p2
      x :+: y -> case (simplifyPath x, simplifyPath y) of
                    (Fail, _)   -> Fail
                    (_, Fail)   -> Fail    
                    (Empty, p1) -> p1
                    (p2, Empty) -> p2
                    (p1, p2)    -> p1 :+: p2
      Step a  -> Step a
      Fail    -> Fail
      Empty   -> Empty

tailSharingBy :: (a -> a -> Ordering) -> Path a -> Path a
tailSharingBy compf path =
   case simplifyPath path of 
      Empty -> Empty
      Fail  -> Fail
      p     -> rec p
      
 where
  eqf x y = compf x y == EQ
  eqfM x y = compfM x y == EQ
  compfM Nothing  Nothing  = EQ
  compfM (Just x) (Just y) = compf x y
  compfM m1       _        = if isJust m1 then GT else LT
  
  -- invariant: rec does not have Empty's or Fail's
  rec (Step a)    = Step a
  rec (p1 :+: p2) = p1 :+: rec p2 
  rec path =  
     let sharedTail = map (\((p, tl):rest) -> combine (p:map fst rest) tl)
                    . groupBy (\x y -> snd x  `eqfM`  snd y)
                    . sortBy  (\x y -> snd x `compfM` snd y)
                    $ [ (p, lastStep p) |  p <- altPath path ]

         combine paths Nothing   = altList1 paths
         combine paths (Just tl) = 
            case tailSharingBy compf (altList1 (map removeTail paths)) of 
               Fail  -> Fail
               Empty -> Step tl
               path  -> path :+: Step tl
            
     in altList1 sharedTail
  
  altPath :: Path a -> [Path a]
  altPath (p1 :|: p2) = altPath p1 ++ altPath p2
  altPath path        = [path]
  
  lastStep (Step a)    = Just a
  lastStep (p1 :+: p2) = lastStep p2
  lastStep (p1 :|: p2) = do a <- lastStep p1
                            b <- lastStep p2
                            if a `eqf` b 
                              then Just a
                              else Nothing

  removeTail (Step a)    = Empty
  removeTail (p1 :+: p2) = p1 :+: removeTail p2
  removeTail (p1 :|: p2) = removeTail p1 :|: removeTail p2

flattenPath :: Path a -> [[a]]
flattenPath path = 
   case path of 
      Empty     -> [[]]
      Fail      -> []
      Step a    -> [[a]]
      p1 :+: p2 -> [ as ++ bs | as <- flattenPath p1, bs <- flattenPath p2]
      p1 :|: p2 -> flattenPath p1 ++ flattenPath p2

-- returns a list with 'smallest minimal sets'
minimalSets :: (a -> a -> Bool) -> Path a -> [[a]]
minimalSets eqF = rec where

   -- invariant: rec returns lists with the same length                
   rec path =
      case simplifyPath path of 
         Empty -> []
         Fail  -> [[]]
         p     -> 
            let a    = head (steps p)
                sol1 = rec (changeStep (\b -> if a `eqF` b then Empty else Step b) p) 
                sol2 = [ a : set
                       | set <- rec (changeStep (\b -> if a `eqF` b then Fail else Step b) p) 
                       ]
            in case (sol1, sol2) of
                  (x:_, y:_) -> 
                     case length x `compare` length y of
                        LT -> sol1
                        EQ -> sol1 ++ sol2
                        GT -> sol2
                  _ -> sol1 ++ sol2

removeSomeDuplicates :: (a -> a -> Bool) -> Path a -> Path a
removeSomeDuplicates eqF = simplifyPath . rec where
   rec path = 
      case path of
         Step a :+: p -> Step a :+: rec (changeStep (\a' -> if a `eqF` a' then Empty else Step a') p)
         Step a :|: p -> Step a :|: rec (changeStep (\a' -> if a `eqF` a' then Fail  else Step a') p)
         (p1 :+: p2) :+: p3 -> rec (p1 :+: (p2 :+: p3))
         (p1 :|: p2) :|: p3 -> rec (p1 :|: (p2 :|: p3))
         p1 :+: p2 -> rec p1 :+: rec p2
         p1 :|: p2 -> rec p1 :|: rec p2
         _ -> path
         
participationMap :: Ord a => Path a -> (Integer, FiniteMap a Integer)
participationMap path = 
   case path of
      Empty     -> (1, emptyFM)
      Fail      -> (0, emptyFM)
      Step a    -> (1, unitFM a 1)
      p1 :+: p2 -> let (i1, fm1) = participationMap p1 
                       (i2, fm2) = participationMap p2
                       fm1'      = mapFM (const (*i2)) fm1
                       fm2'      = mapFM (const (*i1)) fm2
                   in (i1 * i2, plusFM_C (\j1 j2 -> j1 + j2 - ((j1*j2) `div` (i1*i2))) fm1' fm2')
      p1 :|: p2 -> let (i1, fm1) = participationMap p1 
                       (i2, fm2) = participationMap p2
                   in (i1 + i2, plusFM_C (+) fm1 fm2)
