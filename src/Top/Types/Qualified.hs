-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A qualified type is a plain type together with a list of predicates.
--
-----------------------------------------------------------------------------

module Top.Types.Qualified where

import Top.Types.Basics
import Top.Types.Substitution
import Data.List (union, (\\), sort)

infix 2 :=>

-- |A qualified type ('QType') is a monotype with some predicates about its type variables.
data QType      = Predicates :=> Tp
type Predicates = [Predicate]
data Predicate  = Predicate String Tp 
   deriving Eq

-- |A qualified type is ambiguous if there is a predicate that contains a type variable which 
-- does not occur in the type.
isAmbiguous :: QType -> Bool
isAmbiguous (ps :=> tp) = 
   not (null (ftv ps \\ ftv tp))

-- |A predicate is ground if it does not contain type variables.
isGround :: Predicate -> Bool
isGround (Predicate _ tp) = null (ftv tp)

-- |Tests if a qualified type has predicates.s
hasPredicates :: QType -> Bool
hasPredicates (ps :=> _) = not (null ps)

showContext :: Predicates -> String
showContext []  = ""
showContext [p] = show p
showContext ps  = let list = foldr1 (\x y -> x++", "++y) (sort (map show ps))
                  in "(" ++ list ++ ")" 

instance Show QType where
   show (ps :=> tp)
     | null ps   = show tp
     | otherwise = showContext ps ++ " => " ++ show tp
   
instance Show Predicate where
   show (Predicate s tp) = if priorityOfType tp == 2 
                             then s ++ " " ++ show tp
                             else s ++ " (" ++ show tp ++ ")"
                        
instance Substitutable QType where
   sub |-> (ps :=> tp) = (sub |-> ps :=> sub |-> tp)
   ftv     (ps :=> tp) = ftv ps `union` ftv tp

instance Substitutable Predicate where
   sub |-> (Predicate s tp) = Predicate s (sub |-> tp)
   ftv     (Predicate _ tp) = ftv tp
