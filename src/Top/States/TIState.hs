-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Additional state information that should be stored in order to perform
-- type inference (a counter for fresh type variables, known type synonyms, and
-- a list of predicates).
--
-----------------------------------------------------------------------------

module Top.States.TIState where

import Top.Types
import Data.FiniteMap

---------------------------------------------------------------------
-- * A state for type inferencers

-- |A type class for monads that contain a type inference state.
class Monad m => HasTI m info | m -> info where  
   tiGet :: m (TIState info)
   tiPut :: TIState info -> m ()

tiModify :: HasTI m info => (TIState info -> TIState info) -> m ()
tiModify f = do a <- tiGet ; tiPut (f a)

tiGets :: HasTI m info => (TIState info -> a) -> m a
tiGets   f = do a <- tiGet ; return (f a)

data TIState info = TIState
   { counter       :: Int                    -- ^ A counter for fresh type variables
   , synonyms      :: OrderedTypeSynonyms    -- ^ All known type synonyms
   , predicates    :: [(Predicate, info)]    -- ^ A list of predicates
   }

-- |An empty type inference state.
emptyTI :: TIState info
emptyTI = TIState
   { counter      = 0
   , synonyms     = noOrderedTypeSynonyms
   , predicates   = [] 
   }

instance Show (TIState info) where
   show s = unlines [ "counter    = " ++ show (counter s)
                    , "synonyms   = " ++ concat [ t++"; " | t <- keysFM (fst (synonyms s)) ]
                    , "predicates = " ++ concat [ show p++"; " | (p,_) <- predicates s ]
                    ]  
   
---------------------------------------------------------------------
-- * Unique counter

getUnique      :: HasTI m info => m Int
setUnique      :: HasTI m info => Int -> m ()  
nextUnique     :: HasTI m info => m Int
zipWithUniques :: HasTI m info => (Int -> a -> b) -> [a] -> m [b]

getUnique   = tiGets counter
setUnique i = tiModify (\x -> x { counter = i })    

nextUnique = 
   do i <- getUnique
      setUnique (i+1)
      return i

zipWithUniques f as = 
   do i <- getUnique
      setUnique (i+length as)
      return (zipWith f [i..] as)   
   
---------------------------------------------------------------------
-- * Type synonyms

setTypeSynonyms :: HasTI m info => OrderedTypeSynonyms -> m ()
getTypeSynonyms :: HasTI m info => m OrderedTypeSynonyms 

setTypeSynonyms xs = tiModify (\x -> x { synonyms = xs })
getTypeSynonyms    = tiGets synonyms
   
---------------------------------------------------------------------
-- * Predicates
   
getPredicates :: HasTI m info => m [(Predicate, info)]
addPredicate  :: HasTI m info => (Predicate, info) -> m ()
setPredicates :: HasTI m info => [(Predicate, info)] -> m ()

getPredicates    = tiGets predicates
addPredicate  p  = tiModify (\x -> x { predicates = p : predicates x })
setPredicates ps = tiModify (\x -> x { predicates = ps })
