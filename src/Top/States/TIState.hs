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
import Top.States.States
import Top.States.BasicState
import Top.States.SubstState
import Top.Qualifiers.QualifierMap
import Data.FiniteMap
import Data.List

---------------------------------------------------------------------
-- * A state for type inferencers

-- |A type class for monads that contain a type inference state.
class Monad m => HasTI m info | m -> info where  
   tiGet :: m (TIState info)
   tiPut :: TIState info -> m ()

tiModify :: HasTI m info => (TIState info -> TIState info) -> m ()
tiModify f = do a <- tiGet ; tiPut (f a)

tiGets :: HasTI m info => (TIState info -> a) -> m a
tiGets f = do a <- tiGet ; return (f a)

data TIState info = TIState
   { counter      :: Int                         -- ^ A counter for fresh type variables
   , synonyms     :: OrderedTypeSynonyms         -- ^ All known type synonyms
   , classenv     :: ClassEnvironment            -- ^ All known type classes and instances
   , predicates   :: QualifierMap Predicate info -- ^ Type class assertions
   , skolems      :: [(Int, info)]               -- ^ List of skolem constants
   }

type SchemeMap qs = FiniteMap Int (Scheme qs)

-- |An empty type inference state.
instance Show info => Empty (TIState info) where
   empty = TIState
      { counter      = 0
      , synonyms     = noOrderedTypeSynonyms
      , classenv     = emptyClassEnvironment
      , predicates   = makeQualifierMap globalQM
      , skolems      = []
      }

instance Show info => Show (TIState info) where
   show s = unlines [ "counter: " ++ show (counter s)
                    , "skolem constants: " ++ show (skolems s)
                    , "synonyms: " ++ concat [ t++"; " | t <- keysFM (fst (synonyms s)) ]
                    , "classenv: " ++ concat [ t++"; " | t <- keysFM (classenv s) ]
                    , "type class assertions:"
                    , show (predicates s)
                    ]  

instance Show info => IsState (TIState info)

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
-- * Class environment

setClassEnvironment :: HasTI m info => ClassEnvironment -> m ()
getClassEnvironment :: HasTI m info => m ClassEnvironment

setClassEnvironment xs = tiModify (\x -> x { classenv = xs })
getClassEnvironment    = tiGets classenv

---------------------------------------------------------------------
-- * Type class assertions

instance HasTI m info => Has m (QualifierMap Predicate info) where
   get   = tiGets predicates
   put x = tiModify (\s -> s { predicates = x })

getPredicates :: HasTI m info => m Predicates -- only to return all predicates
getPredicates = 
   do syns     <- getTypeSynonyms
      classEnv <- getClassEnvironment
      ps       <- gets (\qms -> getQualifiers qms ++ getGeneralizedQs qms)
      return (fst (contextReduction syns classEnv (map fst ps)))
  
---------------------------------------------------------------------
-- * Instantiation and skolemization

instantiateM :: (HasTI m info, Substitutable a) => Forall a -> m a
instantiateM fa =
   do unique <- getUnique
      let (newUnique, a) = instantiate unique fa
      setUnique newUnique
      return a
      
skolemizeTruly :: (HasTI m info, Substitutable a) => Forall a -> m a
skolemizeTruly fa =
   do unique <- getUnique
      let (newUnique, a) = skolemize unique fa
      setUnique newUnique
      return a

skolemizeFaked :: (HasTI m info, Substitutable a) => info -> Forall a -> m a
skolemizeFaked info fa =
   do unique <- getUnique
      let (newUnique, a) = instantiate unique fa
          list = zip [ unique .. newUnique-1 ] (repeat info)
      tiModify (\s -> s { skolems = list ++ skolems s })
      setUnique newUnique
      return a
      
getSkolemSubstitution :: HasTI m info => m FiniteMapSubstitution
getSkolemSubstitution =
   tiGets (listToSubstitution . map (\(i, _) -> (i, makeSkolemConstant i)) . skolems)

-- |First, make the substitution consistent. Then check the skolem constants
makeConsistent :: (HasTI m info, HasBasic m info, HasSubst m info) => m ()
makeConsistent      = makeSubstConsistent >> checkSkolems
 
checkSkolems :: (HasTI m info, HasSubst m info, HasBasic m info) => m ()
checkSkolems =
   do list <- tiGets skolems
      tps  <- mapM (findSubstForVar . fst) list
      
      -- skolem constant versus type constant
      let (ok, errs) = partition (isTVar . snd) (zip list tps)
      mapM (\((_, info), _) -> addLabeledError skolemVersusConstantLabel info) errs
      
      -- skolem constant versus a different skolem constant
      let okList = groupBy (\x y -> snd x == snd y) (sortBy (\x y -> snd x `compare` snd y) ok)
      xss <- let f [(pair, _)] = return [pair]
                 f pairs = 
                    do addLabeledError skolemVersusSkolemLabel (snd . fst . head $ pairs)
                       return []
             in mapM f okList
      
      tiModify (\s -> s { skolems = concat xss })
     
skolemVersusConstantLabel :: ErrorLabel
skolemVersusConstantLabel = ErrorLabel "skolem versus constant" 

skolemVersusSkolemLabel :: ErrorLabel
skolemVersusSkolemLabel = ErrorLabel "skolem versus skolem" 