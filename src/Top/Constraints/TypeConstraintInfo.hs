module Top.Constraints.TypeConstraintInfo where

import Top.Types

class Show info => TypeConstraintInfo info where
   equalityTypePair    :: (Tp, Tp)  -> info -> info
   ambiguousPredicate  :: Predicate -> info -> info
   unresolvedPredicate :: Predicate -> info -> info
   
   -- default definitions
   equalityTypePair _    = id
   ambiguousPredicate _  = id
   unresolvedPredicate _ = id
   
class TypeConstraintInfo info => PolyTypeConstraintInfo qs info | info -> qs where
   originalTypeScheme  :: Forall (Qualification qs Tp) -> info -> info

   -- default definition
   originalTypeScheme _  = id