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
import Top.Types.Qualification
import Top.Types.Quantification
import Data.List (union, (\\), sort)

-- |A qualified type ('QType') is a monotype with some predicates about its type variables.
type QType      = Qualification Predicate Tp
type Predicates = [Predicate]
data Predicate  = Predicate String Tp deriving Eq

instance ShowQuantors Predicate
   
instance Show Predicate where
   show (Predicate s tp) = if priorityOfType tp == 2 
                             then s ++ " " ++ show tp
                             else s ++ " (" ++ show tp ++ ")"                       

instance Substitutable Predicate where
   sub |-> (Predicate s tp) = Predicate s (sub |-> tp)
   ftv     (Predicate _ tp) = ftv tp