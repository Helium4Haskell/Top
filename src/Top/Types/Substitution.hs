-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- This module contains a data type to represent (plain) types, some basic 
-- functionality for types, and an instance for Show.
--
-----------------------------------------------------------------------------

module Top.Types.Substitution where

import Top.Types.Basics
import Data.Array
import Data.List (union, (\\))
import Data.FiniteMap
import Utils (internalError)

----------------------------------------------------------------------
-- * Substitutions and substitutables

infix 4 |->

class Substitution s where
   lookupInt   :: Int -> s -> Tp         -- lookup the type of a type variable in a substitution   
   removeDom   :: [Int] -> s -> s        -- remove from the domain of the substitution
   restrictDom :: [Int] -> s -> s        -- restrict the domain of the substitution
   dom         :: s -> [Int]             -- domain of substitution
   cod         :: s -> Tps               -- co-domain of substitution
   
class Substitutable a where 
   (|->) :: Substitution s => s -> a -> a    -- apply substitution
   ftv    :: a -> [Int]                      -- free type variables   
   
   _ |-> a   = a        -- default definition (do nothing)
   ftv _     = []       -- default definition (do nothing)

-- |The next type variable that is not free (default is zero)
nextFTV :: Substitutable a => a -> Int
nextFTV a = case ftv a of
               [] -> 0
               is -> maximum is + 1

----------------------------------------------------------------------
-- * Substitution instances 

-- |A substitution represented by a finite map.
type FiniteMapSubstitution = FiniteMap Int Tp

instance Substitution FiniteMapSubstitution where

   lookupInt i fm = lookupWithDefaultFM fm (TVar i) i
   removeDom      = flip delListFromFM
   restrictDom is = filterFM (\i _ -> i `elem` is)
   
   dom = keysFM
   cod = eltsFM 

emptySubst :: FiniteMapSubstitution
emptySubst = emptyFM

-- |Compose two finite map substitutions: safe.
-- Note for 'plusFM': bindings in right argument shadow those in the left
(@@) :: FiniteMapSubstitution -> FiniteMapSubstitution -> FiniteMapSubstitution
fm1 @@ fm2 = fm1 `plusFM` mapFM (\_ t -> fm1 |-> t) fm2  

-- |Compose two finite map substitutions: quick and dirty!
(@@@) :: FiniteMapSubstitution -> FiniteMapSubstitution -> FiniteMapSubstitution
(@@@) = plusFM 

singleSubstitution :: Int -> Tp -> FiniteMapSubstitution
singleSubstitution = unitFM

listToSubstitution :: [(Int,Tp)] -> FiniteMapSubstitution
listToSubstitution = listToFM

-- |A fixpoint is computed when looking up the target of a type variable in this substitution. 
-- Combining two substitutions is cheap, whereas a lookup is more expensive than the 
-- normal finite map substitution.
newtype FixpointSubstitution = FixpointSubstitution (FiniteMap Int Tp)

instance Substitution FixpointSubstitution where
   lookupInt i original@(FixpointSubstitution fm) = 
      case lookupFM fm i of
         Just tp | tp == TVar i -> TVar i
                 | otherwise    -> original |-> tp
         Nothing                -> TVar i
   removeDom   is (FixpointSubstitution fm) = FixpointSubstitution (delListFromFM fm is)
   restrictDom is (FixpointSubstitution fm) = let js = keysFM fm \\ is
                                              in FixpointSubstitution (delListFromFM fm js)
   dom (FixpointSubstitution fm) = keysFM fm
   cod (FixpointSubstitution fm) = eltsFM fm
   
instance Show FixpointSubstitution where
   show (FixpointSubstitution fm) = "Fixpoint FiniteMap Substitution: " ++ show (fmToList fm)
 
-- |The empty fixpoint substitution 
emptyFPS :: FixpointSubstitution
emptyFPS = FixpointSubstitution emptyFM
 
-- |Combine two fixpoint substitutions that are disjoint
disjointFPS :: FixpointSubstitution -> FixpointSubstitution -> FixpointSubstitution
disjointFPS (FixpointSubstitution fm1) (FixpointSubstitution fm2) = 
   let notDisjoint = internalError "Substitution" "disjointFPS" "the two fixpoint substitutions are not disjoint"
   in FixpointSubstitution (plusFM_C notDisjoint fm1 fm2)   
 
----------------------------------------------------------------------
-- * Wrapper for substitutions

wrapSubstitution :: Substitution substitution => substitution -> WrappedSubstitution                                     
wrapSubstitution substitution = 
   WrappedSubstitution substitution 
      ( lookupInt
      , removeDom
      , restrictDom
      , dom
      , cod
      )

data WrappedSubstitution = 
   forall a . Substitution a => 
      WrappedSubstitution a 
         ( Int -> a -> Tp   
         , [Int] -> a -> a
         , [Int] -> a -> a
         , a -> [Int]
         , a -> Tps
         )

instance Substitution WrappedSubstitution where
   lookupInt   i  (WrappedSubstitution x (f,_,_,_,_)) = f i x
   removeDom   is (WrappedSubstitution x (_,f,_,_,_)) = wrapSubstitution (f is x)
   restrictDom is (WrappedSubstitution x (_,_,f,_,_)) = wrapSubstitution (f is x)
   dom            (WrappedSubstitution x (_,_,_,f,_)) = f x
   cod            (WrappedSubstitution x (_,_,_,_,f)) = f x

----------------------------------------------------------------------
-- * Substitutables instances
   
instance Substitutable Tp where   
   sub |-> tp = case tp of 
                   TVar i     -> lookupInt i sub
                   TCon _     -> tp
                   TApp t1 t2 -> TApp (sub |-> t1) (sub |-> t2) 
   ftv tp = case tp of
               TVar i     -> [i]
               TCon _     -> []
               TApp t1 t2 -> ftv t1 `union` ftv t2   

instance Substitutable a => Substitutable [a] where
   sub |-> as  = map (sub |->) as
   ftv         = foldr union [] . map ftv   

instance Substitutable a => Substitutable (Maybe a) where
   sub |-> ma = maybe Nothing (Just . (sub |->)) ma
   ftv     ma = maybe [] ftv ma

instance (Substitutable a, Substitutable b) => Substitutable (Either a b) where
   (|->) sub = either (Left . (sub |->)) (Right . (sub |->))
   ftv       = either ftv ftv

instance (Substitutable a, Substitutable b) => Substitutable (a,b) where
   sub |-> (a,b) = (sub |-> a, sub |-> b)
   ftv     (a,b) = ftv a `union` ftv b
