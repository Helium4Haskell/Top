module Top.Constraints.TypeConstraintInfo where

import Top.Types

class Show info => TypeConstraintInfo info where
   equalityTypePair     :: (Tp, Tp)  -> info -> info
   ambiguousPredicate   :: Predicate -> info -> info
   unresolvedPredicate  :: Predicate -> info -> info
   predicateArisingFrom :: (Predicate, info) -> info -> info
   parentPredicate      :: Predicate -> info -> info
   escapedSkolems       :: [Int]     -> info -> info
   neverDirective       :: (Predicate, info) -> info -> info
   closeDirective       :: (String, info)    -> info -> info
   disjointDirective    :: (String, info) -> (String, info) -> info -> info
   
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
   
class TypeConstraintInfo info => PolyTypeConstraintInfo qs info | info -> qs where
   instantiatedTypeScheme :: Forall (Qualification qs Tp) -> info -> info
   skolemizedTypeScheme   :: (Tps, Forall (Qualification qs Tp)) -> info -> info

   -- default definition
   instantiatedTypeScheme _  = id
   skolemizedTypeScheme _    = id