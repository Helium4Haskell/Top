-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.Basics where

import Top.TypeGraph.Paths
import Top.Types
import Utils (internalError)
import Debug.Trace (trace)
import Data.Maybe
import Data.List (sort, nub, partition, intersperse)

---------------------------------------------------------------------------------

debugTypeGraph :: Bool
debugTypeGraph = False

debugTrace :: Monad m => String -> m ()
debugTrace message
   | debugTypeGraph = trace (message++";") (return ())
   | otherwise      = return ()

-----------------------------------------------------------------------------------------

newtype VertexId = VertexId Int deriving (Eq, Ord)
type VertexInfo  = (VertexKind, Maybe Tp)                      
data VertexKind  = VVar | VCon String | VApp VertexId VertexId
   deriving (Show, Eq, Ord)     

instance Show VertexId where
   show (VertexId i) = "<" ++ show i ++ ">"
            
vertexIdToTp :: VertexId -> Tp     
vertexIdToTp (VertexId i) = TVar i
    
data EdgeId        = EdgeId VertexId VertexId
type EdgeInfo info = (EdgeNr, info)
newtype EdgeNr     = EdgeNrX Int deriving (Eq, Ord)
data ChildSide     = LeftChild | RightChild
   deriving (Eq, Ord)

makeEdgeNr :: Int -> EdgeNr
makeEdgeNr = EdgeNrX

instance Show EdgeNr where
   show (EdgeNrX i) = "#" ++ show i

instance Show ChildSide where
   show LeftChild  = "(l)"
   show RightChild = "(r)"

data ParentChild = ParentChild { parent :: VertexId, child :: VertexId, childSide :: ChildSide }
   deriving Eq

instance Show ParentChild where
   show pc = show (child pc) ++ "<-" ++ show (parent pc) ++ show (childSide pc)

instance Ord ParentChild where
   compare pc1 pc2 = compare (child pc1, parent pc1) (child pc2, parent pc2)

type TypeGraphPath info = Path (EdgeId, PathStep info)
data PathStep info 
   = Initial  EdgeNr info
   | Implied  ChildSide VertexId VertexId
   | Child    ChildSide
   
instance Show (PathStep info) where
   show (Initial cnr _)  = "#" ++ show cnr
   show (Implied cs x y) = "(" ++ show cs ++ " : " ++ show (x, y) ++ ")"
   show (Child i)        = "(" ++ show i ++ ")"
   
-- A clique is a set of vertices that are equivalent because their parents are equal
-- Invariant: a clique cannot be empty
newtype Clique  = CliqueX [ParentChild]
type CliqueList = [Clique]

instance Show Clique where
   show (CliqueX xs) = "<" ++ concat (intersperse ", " (map show xs)) ++ ">"

instance Eq Clique where 
   CliqueX xs == CliqueX ys = 
      xs == ys

instance Ord Clique where
   compare (CliqueX xs) (CliqueX ys) = compare xs ys

isSubsetClique :: Clique -> Clique -> Bool
isSubsetClique (CliqueX xs) (CliqueX ys) = rec xs ys 
 where
   rec [] _ = True
   rec _ [] = False
   rec a@(x:xs) (y:ys)
      | x == y    = rec xs ys
      | x > y     = rec a ys
      | otherwise = False
   
isDisjointClique :: Clique -> Clique -> Bool
isDisjointClique (CliqueX xs) (CliqueX ys) = rec xs ys
 where
   rec [] _ = True
   rec _ [] = True
   rec a@(x:xs) b@(y:ys)
      | x == y    = False
      | x > y     = rec a ys
      | otherwise = rec xs b
      
cliqueRepresentative :: Clique -> VertexId
cliqueRepresentative (CliqueX xs) =
   case xs of
      []  -> internalError "Top.TypeGraph.Basics" "cliqueRepresentative" "A clique cannot be empty"
      x:_ -> child x

triplesInClique :: Clique -> [ParentChild]
triplesInClique (CliqueX xs) = xs

childrenInClique :: Clique -> [VertexId]
childrenInClique = map child . triplesInClique

mergeCliques :: CliqueList -> Clique
mergeCliques list = CliqueX (foldr op [] [ xs | CliqueX xs <- list ])
 where
   op xs [] = xs
   op [] ys = ys
   op a@(x:xs) b@(y:ys)
      | x == y = x : op xs ys
      | x < y  = x : op xs b 
      | x > y  = y : op a ys
   
makeClique :: [ParentChild] -> Clique
makeClique list
   | length set < 2 = internalError "Top.TypeGraph.Basics" "makeClique" "incorrect clique"
   | otherwise      = CliqueX set
 where 
   set = sort list

combineCliqueList :: CliqueList -> CliqueList -> CliqueList
combineCliqueList [] ys = ys
combineCliqueList (x:xs) ys =
   let (ys1, ys2) = partition (isDisjointClique x) ys
   in mergeCliques (x:ys2) : combineCliqueList xs ys1
   
instance Show EdgeId where
   show (EdgeId a b) = "("++show a'++"-"++show b'++")"
      where (a',b') = if a <= b then (a,b) else (b,a)
     
instance Eq EdgeId where
   EdgeId a b == EdgeId c d = (a == c && b == d) || (a == d && b == c)
   
instance Ord EdgeId where
   EdgeId a b <= EdgeId c d = order (a,b) <= order (c,d)
      where order (i,j) = if i <= j then (i,j) else (j,i)

-- don't consider the stored information for equality
instance Eq (PathStep info) where
   e1 == e2 = 
      case (e1, e2) of
         (Initial cnr1 _, Initial cnr2 _)       -> cnr1 == cnr2
         (Implied cs1 x1 y1, Implied cs2 x2 y2) -> (cs1, x1, y1) == (cs2, x2, y2)
         (Child i1, Child i2)                   -> i1 == i2
         _                                      -> False
         
-- order edge information without looking at the information that is stored
instance Ord (PathStep info) where
   compare e1 e2 = 
      case (e1, e2) of
         (Initial cnr1 _, Initial cnr2 _)       -> compare cnr1 cnr2
         (Initial _ _, _)                       -> LT
         (_, Initial _ _)                       -> GT
         (Implied cs1 x1 y1, Implied cs2 x2 y2) -> compare (cs1, x1, y1) (cs2, x2, y2)
         (Implied _ _ _, _)                     -> LT
         (_, Implied _ _ _)                     -> GT
         (Child i1, Child i2)                   -> compare i1 i2
