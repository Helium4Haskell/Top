-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A representation of type schemes. A type scheme is a (qualified) type
-- with a number of quantifiers (foralls) in front of it. A partial mapping 
-- from type variable (Int) to their name (String) is preserved.
--
-----------------------------------------------------------------------------

module Top.Types.Schemes where

import Top.Types.Basics
import Top.Types.Quantification
import Top.Types.Qualification
import Top.Types.Substitution
import Top.Types.Synonyms
import Top.Types.Unification
import Top.Types.Classes
import Data.List
import Data.FiniteMap

----------------------------------------------------------------------
-- * Type schemes

-- |A type scheme consists of a list of quantified type variables, a finite map 
-- that partially maps these type variables to their original identifier, and a
-- qualified type.
type TpScheme = Forall QType
type QType    = Qualification Predicates Tp

-- |A type class to convert something into a type scheme
class IsTpScheme a where
   toTpScheme :: a -> TpScheme
   
instance IsTpScheme TpScheme where
   toTpScheme = id

instance IsTpScheme QType where
   toTpScheme = noQuantifiers
   
instance IsTpScheme Tp where
   toTpScheme = noQuantifiers . ([] .=>.)

----------------------------------------------------------------------
-- * Basic functionality for types and type schemes
{-
generalize :: [Int] -> Predicates -> Tp -> TpScheme
generalize monos preds tp = 
   let ftvTP             = ftv tp 
       p (Predicate _ t) = any (`elem` ftvTP) (ftv t)
   in TpScheme (ftv tp \\ monos) [] (filter p preds :=> tp)
                        
generalizeAll :: Tp -> TpScheme
generalizeAll = generalize [] []

instantiate :: Int -> TpScheme -> (Int, Predicates, Tp)
instantiate unique (TpScheme qs _ (ps :=> tp)) = 
   let sub = listToSubstitution (zip qs (map TVar [unique..]))
   in (unique + length qs, sub |-> ps, sub |-> tp)  
   
instantiateWithNameMap :: Int -> TpScheme -> (Int, Predicates, Tp) -- get rid of this function.
instantiateWithNameMap unique (TpScheme qs nm qtp) = 
   let sub = listToSubstitution [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
   in instantiate unique (TpScheme (qs \\ (map fst nm)) [] (sub |-> qtp))

-- |Use a magic number to instantiate a type scheme. (dangerous!)
unsafeInstantiate :: TpScheme -> Tp
unsafeInstantiate scheme = tp
   where magicNumber = 123456789
         (_, _, tp)  = instantiate magicNumber scheme
-}
-- |Determine the arity of a type scheme.    
arityOfTpScheme :: TpScheme -> Int
arityOfTpScheme = arityOfTp . unqualify . unquantify
{-
-- |Is the type scheme overloaded (does it contain predicates)?
isOverloaded :: TpScheme -> Bool
isOverloaded (TpScheme _ _ (xs :=> _)) = not (null xs)

freezeFreeTypeVariables :: TpScheme -> TpScheme
freezeFreeTypeVariables scheme = 
   let sub = listToSubstitution (map f (ftv scheme))
       f i = (i, TCon ('_' : show i))
   in sub |-> scheme

-- |Still to be defined......
isInstanceOf :: Tp -> TpScheme -> Bool
isInstanceOf _ _ = True -- !!!!!!!!!!!! undefined

genericInstanceOf :: OrderedTypeSynonyms -> ClassEnvironment -> TpScheme -> TpScheme -> Bool
genericInstanceOf synonyms classes scheme1 scheme2 =
   let -- monomorphic type variables are treated as constants
       s1 = freezeFreeTypeVariables scheme1
       s2 = freezeFreeTypeVariables scheme2
       -- substitution to fix the type variables in the first type scheme
       sub         = listToSubstitution (zip (getQuantifiers s1) [ TCon ('+':show i) | i <- [0 :: Int ..]])
       ps1 :=> tp1 = sub |-> getQualifiedType s1
       (_,ps2,tp2) = instantiate 123456789 s2
   in case mguWithTypeSynonyms synonyms tp1 tp2 of
         Left _         -> False
         Right (_,sub2) -> entailList synonyms classes ps1 (sub2 |-> ps2)
-}
genericInstanceOf :: OrderedTypeSynonyms -> ClassEnvironment -> TpScheme ->  TpScheme -> Bool
genericInstanceOf synonyms classes scheme1 scheme2 = 
   let -- monomorphic type variables are treated as constants
       s1 = skolemizeFTV scheme1
       s2 = skolemizeFTV scheme2
       -- substitution to fix the type variables in the first type scheme
       sub        = listToSubstitution (zip (quantifiers s1) [ TCon ('+':show i) | i <- [0 :: Int ..]])
       (ps1, tp1) = split (sub |-> unquantify s1)
       (ps2, tp2) = split (snd (instantiate 123456789 s2))
   in case mguWithTypeSynonyms synonyms tp1 tp2 of
         Left _         -> False
         Right (_,sub2) -> entailList synonyms classes ps1 (sub2 |-> ps2)

makeScheme :: [Int] -> Predicates -> Tp -> TpScheme
makeScheme monos preds tp = 
   let is  = ftv tp \\ monos
       p   = any (`elem` is) . ftv
   in quantify is (filter p preds .=>. tp)   

instantiateWithNameMap :: Int -> TpScheme -> (Int, Predicates, Tp) -- get rid of this function.
instantiateWithNameMap unique (Quantification (qs,nm,qtp)) = 
   let sub = listToSubstitution [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
       (u, qtp') = instantiate unique (Quantification (qs \\ (map fst nm), [], sub |-> qtp))
       (ps, tp) = split qtp'
   in (u, ps, tp)

instance (ShowQualifiers q, Show a) => ShowQuantors (Qualification q a)

-- |A sigma is a type scheme or a type scheme variable
type Scheme qs = Forall (Qualification qs Tp)

data Sigma qs  = SigmaVar    SigmaVar 
               | SigmaScheme (Scheme qs)
type SigmaVar  = Int

instance (ShowQualifiers qs, Substitutable qs) => Show (Sigma qs) where
   show (SigmaVar i)    = "s" ++ show i
   show (SigmaScheme s) = show s

instance Substitutable qs => Substitutable (Sigma qs) where   
   sub |-> sv@(SigmaVar _) = sv 
   sub |-> (SigmaScheme s) = SigmaScheme (sub |-> s)   
   
   ftv (SigmaVar i)    = []
   ftv (SigmaScheme s) = ftv s 
   {-
-- |A type class to convert something into a "sigma" 

class IsSigma a qs where
   toSigma :: a -> Sigma qs
   
instance IsSigma (Sigma qs) qs where
   toSigma = id

instance IsSigma (Scheme qs) qs where
   toSigma = SigmaScheme

instance IsSigma (Qualification qs Tp) qs where
   toSigma = SigmaScheme . noQuantifiers -}

-- |A substitution for type scheme variables
type TpSchemeMap = FiniteMap SigmaVar TpScheme