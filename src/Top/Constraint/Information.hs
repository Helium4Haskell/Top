{-# OPTIONS -fglasgow-exts #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  bastiaan@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Constraint.Information where

import Top.Types

instance TypeConstraintInfo () () where emptyInfo = ()
instance PolyTypeConstraintInfo () ()

instance TypeConstraintInfo String String where emptyInfo = ""
instance PolyTypeConstraintInfo String String

class (Show info, Ord info, Ord id) => TypeConstraintInfo info id | info -> id where
   equalityTypePair     :: (Tp, Tp)  -> info -> info
   ambiguousPredicate   :: Predicate -> info -> info
   unresolvedPredicate  :: Predicate -> info -> info
   predicateArisingFrom :: (Predicate, info) -> info -> info
   parentPredicate      :: Predicate -> info -> info
   escapedSkolems       :: [Int]     -> info -> info
   neverDirective       :: (Predicate, info) -> info -> info
   closeDirective       :: (String, info)    -> info -> info
   disjointDirective    :: (String, info) -> (String, info) -> info -> info
   overloadedIdentifier :: info -> Maybe id
   -- GvdG::  TODO:: To be removed!!!!!
   emptyInfo            :: info
   
   -- default definitions
   equalityTypePair _     = id
   ambiguousPredicate _   = id
   unresolvedPredicate _  = id
   predicateArisingFrom _ = id
   parentPredicate _      = id
   escapedSkolems _       = id
   neverDirective _       = id
   closeDirective _       = id
   disjointDirective _ _  = id
   overloadedIdentifier _ = Nothing
   
class TypeConstraintInfo info id => PolyTypeConstraintInfo info id where
   instantiatedTypeScheme :: Forall (Qualification Predicates Tp) -> info -> info
   skolemizedTypeScheme   :: (Tps, Forall (Qualification Predicates Tp)) -> info -> info

   -- default definition
   instantiatedTypeScheme _  = id
   skolemizedTypeScheme _    = id
