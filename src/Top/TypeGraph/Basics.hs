-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.Basics where

import Debug.Trace (trace)
import Data.Maybe
import Data.List

---------------------------------------------------------------------------------

debugTypeGraph :: Bool
debugTypeGraph = False

debugTrace :: Monad m => String -> m ()
debugTrace message
   | debugTypeGraph = trace (message++";") (return ())
   | otherwise      = return ()

-----------------------------------------------------------------------------------------

type VertexID      = Int
type VertexInfo    = ( VertexKind 
                     , Maybe (String,[VertexID])  -- original type synonym
                     )                      
data VertexKind = VVar
                | VCon String
                | VApp VertexID VertexID
   deriving (Show, Eq, Ord)                
                     
data EdgeID        = EdgeID VertexID VertexID
data EdgeInfo info = Initial Int {- constraint number -} info
                   | Implied Int VertexID VertexID
                   | Child Int
type Clique        = (Int, [(VertexID,VertexID)] )
type Cliques       = (Int,[[(VertexID,VertexID)]])

instance Show (EdgeInfo info) where
   show (Initial cnr _)   = "#" ++ show cnr
   show (Implied i p1 p2) = "(" ++ show i ++ " : " ++ show (p1,p2) ++ ")"
   show (Child i)         = "(" ++ show i ++ ")"

instance Show EdgeID where
   show (EdgeID a b) = "("++show a++"-"++show b++")"
     -- where (a',b') = if a <= b then (a,b) else (b,a)
     
instance Eq EdgeID where
   EdgeID a b == EdgeID c d = (a == c && b == d) || (a == d && b == c)
   
instance Ord EdgeID where
   EdgeID a b <= EdgeID c d = order (a,b) <= order (c,d)
      where order (i,j) = if i <= j then (i,j) else (j,i)

-- don't consider the stored information for equality
instance Eq (EdgeInfo info) where
   e1 == e2 = 
      case (e1, e2) of
         (Initial cnr1 _, Initial cnr2 _)     -> cnr1 == cnr2
         (Implied i1 a1 b1, Implied i2 a2 b2) -> (i1,a1,b1) == (i2,a2,b2)
         (Child i1, Child i2)                 -> i1 == i2
         _                                    -> False
         
-- order edge information without looking at the information that is stored
instance Ord (EdgeInfo info) where
   compare e1 e2 = 
      case (e1, e2) of
         (Initial cnr1 _, Initial cnr2 _)     -> compare cnr1 cnr2
         (Initial _ _, _)                     -> LT
         (_, Initial _ _)                     -> GT
         (Implied i1 a1 b1, Implied i2 a2 b2) -> compare (i1,a1,b1) (i2,a2,b2)
         (Implied _ _ _, _)                   -> LT
         (_, Implied _ _ _)                   -> GT
         (Child i1, Child i2)                 -> compare i1 i2
