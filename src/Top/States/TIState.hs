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
import Top.Constraints.TypeConstraintInfo
import Top.States.States
import Top.States.BasicState
import Top.States.SubstState
import Top.Qualifiers.QualifierMap
import Data.FiniteMap
import Data.List
import Control.Monad

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
   { counter             :: Int                         -- ^ A counter for fresh type variables
   , synonyms            :: OrderedTypeSynonyms         -- ^ All known type synonyms
   , classenv            :: ClassEnvironment            -- ^ All known type classes and instances
   , predicates          :: QualifierMap Predicate info -- ^ Type class assertions
   , typeclassDirectives :: TypeClassDirectives info    -- ^ Directives for type class assertions
   , skolems             :: [([Int], info, Tps)]        -- ^ List of skolem constants
   }

type SchemeMap qs = FiniteMap Int (Scheme qs)

-- |An empty type inference state.
instance Show info => Empty (TIState info) where
   empty = TIState
      { counter             = 0
      , synonyms            = noOrderedTypeSynonyms
      , classenv            = emptyClassEnvironment
      , predicates          = makeQualifierMap globalQM
      , typeclassDirectives = empty
      , skolems             = []
      }

instance Show info => Show (TIState info) where
   show s = unlines [ "counter: " ++ show (counter s)
                    , "skolem constants: " ++ show (skolems s)
                    , "synonyms: " ++ concat [ t++"; " | t <- keysFM (fst (synonyms s)) ]
                    , "classenv: " ++ concat [ t++"; " | t <- keysFM (classenv s) ]
                    , "type class directives: " ++ show (typeclassDirectives s)
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

getPredicates :: HasTI m info => m Predicates -- ??
getPredicates = 
   do syns     <- getTypeSynonyms
      classEnv <- getClassEnvironment
      ps       <- gets (\qms -> getQualifiers qms ++ getGeneralizedQs qms ++ getAssumptions qms)
      return (fst (contextReduction syns classEnv (map fst ps)))

---------------------------------------------------------------------
-- * Type class directives

type NeverDirective    info = (Predicate, info)
type CloseDirective    info = (String, info)
type DisjointDirective info = ([String], info)
type DefaultDirective  info = (String, (Tps, info))

data TypeClassDirectives info = TypeClassDirectives 
   { neverDirectives    :: [NeverDirective info]
   , closeDirectives    :: [CloseDirective info]
   , disjointDirectives :: [DisjointDirective info]
   , defaultDirectives  :: [DefaultDirective info]
   }

instance Show info => Show (TypeClassDirectives info) where
   show tcd = 
      let f title pf xs
             | null xs   = ""
             | otherwise = "\n   "++title++": "++concat (intersperse "; " (map pf xs))
          p1 (x, _) = show x
          p2 (x, _) = x
          p3 (x, _) = concat (intersperse "," x)
          p4 (cn, (tps, _)) = cn ++ " ("++concat (intersperse "," (map show tps)) ++ ")"
      in f "never"    p1 (neverDirectives tcd)    ++
         f "close"    p2 (closeDirectives tcd)    ++
         f "disjoint" p3 (disjointDirectives tcd) ++
         f "default"  p4 (defaultDirectives tcd) 
         
instance Empty (TypeClassDirectives info) where
   empty = TypeClassDirectives { neverDirectives = [], closeDirectives = [], disjointDirectives = [], defaultDirectives = [] }

changeTCD :: HasTI m info => (TypeClassDirectives info -> TypeClassDirectives info) -> m ()
changeTCD f = 
   tiModify (\s -> s { typeclassDirectives = f (typeclassDirectives s) })

addNeverDirective :: HasTI m info => NeverDirective info -> m ()
addNeverDirective x = 
   changeTCD (\s -> s { neverDirectives = x : neverDirectives s })
  
addCloseDirective :: HasTI m info => CloseDirective info -> m ()
addCloseDirective x =
   changeTCD (\s -> s { closeDirectives = x : closeDirectives s })

addDisjointDirective :: HasTI m info => DisjointDirective info -> m ()
addDisjointDirective x =
   changeTCD (\s -> s { disjointDirectives = x : disjointDirectives s })

addDefaultDirective :: HasTI m info => DefaultDirective info -> m ()
addDefaultDirective x =
   changeTCD (\s -> s { defaultDirectives = x : defaultDirectives s })

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

skolemizeFaked :: (HasTI m info, Substitutable a) => info -> Tps -> Forall a -> m a
skolemizeFaked info monos fa =
   do unique <- getUnique
      let (newUnique, a) = instantiate unique fa
          new = ([ unique .. newUnique-1 ], info, monos)
      tiModify (\s -> s { skolems = new : skolems s })
      setUnique newUnique
      return a

getSkolemSubstitution :: HasTI m info => m FiniteMapSubstitution
getSkolemSubstitution =
   tiGets (\s -> listToSubstitution [ (i, makeSkolemConstant i) | (is, _, _) <- skolems s, i <- is ]) 
  
-- |First, make the substitution consistent. Then check the skolem constants(?)
makeConsistent :: (HasTI m info, HasBasic m info, HasSubst m info) => m ()
makeConsistent = makeSubstConsistent -- >> checkSkolems
 
checkSkolems :: (HasTI m info, HasSubst m info, HasBasic m info, TypeConstraintInfo info) => m ()
checkSkolems = 
   do xs    <- tiGets skolems
      list1 <- let f (is, info, monos) = 
                      do tps <- mapM findSubstForVar is
                         return (zip is tps, (info, monos))
               in mapM f xs
      
      -- skolem constant versus type constant
      let (list2, errs) = partition (all (isTVar . snd) . fst) list1
      mapM_ (addLabeledError skolemVersusConstantLabel . fst . snd) errs
      
      -- skolem constant versus a different skolem constant
      let problems = filter ((>1) . length)
                   . groupBy (\x y -> fst x == fst y)
                   . sortBy  (\x y -> fst x `compare` fst y)
                   $ [ (i, info) | (pairs, (info, _)) <- list2, (_, TVar i) <- pairs ]
          list3 = let is = concatMap (map fst) problems
                      p (pairs, _) = null (ftv (map snd pairs) `intersect` is)
                  in filter p list2
      mapM_  (addLabeledError skolemVersusSkolemLabel . snd . head) problems

      -- escaping skolem constants
      list4 <- let op rest this@(pairs, (info, monos)) =
                      do monos' <- applySubst monos
                         case ftv monos' `intersect` ftv (map snd pairs) of
                            []  -> return (this:rest)
                            esc -> do addLabeledError escapingSkolemLabel (escapedSkolems esc info)
                                      return rest
               in foldM op [] list3

      let new = [ (map fst pairs, info, monos) | (pairs, (info, monos)) <- list4 ]
      tiModify (\s -> s { skolems = new })
     
skolemVersusConstantLabel :: ErrorLabel
skolemVersusConstantLabel = ErrorLabel "skolem versus constant" 

skolemVersusSkolemLabel :: ErrorLabel
skolemVersusSkolemLabel = ErrorLabel "skolem versus skolem" 

escapingSkolemLabel :: ErrorLabel
escapingSkolemLabel = ErrorLabel "escaping skolem"