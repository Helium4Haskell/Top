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
import Top.Types.Qualified
import Top.Types.Substitution
import Top.Types.Synonyms
import Top.Types.Unification
import Top.Types.Classes
import Data.List

----------------------------------------------------------------------
-- * Type schemes

-- |A type scheme consists of a list of quantified type variables, a finite map 
-- that partially maps these type variables to their original identifier, and a
-- qualified type.
data TpScheme = TpScheme 
                { getQuantifiers     :: [Int]             
                , getNameMap         :: [(Int,String)]
                , getQualifiedType   :: QType
                }

-- |List of unique identifiers.(a, b, .., z, a1, b1 .., z1, a2, ..)
variableList :: [String]
variableList =  [ [x]        | x <- ['a'..'z'] ]
             ++ [ (x:show i) | i <- [1 :: Int ..], x <- ['a'..'z'] ]

instance Show TpScheme where
   show (TpScheme quantifiers namemap qtype) = 
      let sub1     = filter ((`elem` quantifiers) . fst) namemap 
          unknown  = quantifiers \\ map fst sub1
          sub2     = zip unknown [ s | s <- variableList, s `notElem` map snd sub1 ]
          subTotal = listToSubstitution [ (i, TCon s) | (i, s) <- sub1 ++ sub2 ]
      in show (subTotal |-> qtype)

instance Substitutable TpScheme where
   sub |-> (TpScheme quantifiers namemap qtype) = TpScheme quantifiers namemap (removeDom quantifiers sub |-> qtype)
   ftv     (TpScheme quantifiers _ qtype) = ftv qtype \\ quantifiers

----------------------------------------------------------------------
-- * Basic functionality for types and type schemes

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

-- |Determine the arity of a type scheme.    
arityOfTpScheme :: TpScheme -> Int
arityOfTpScheme (TpScheme _ _ (_ :=> tp)) = arityOfTp tp

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
