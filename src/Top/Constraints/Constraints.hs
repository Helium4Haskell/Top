{-# OPTIONS -fallow-undecidable-instances #-}
-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A data type to represent constraints in general, and a type class for
-- constraints that are solvable.
--
-----------------------------------------------------------------------------

module Top.Constraints.Constraints where

import Top.Types (Substitutable(..))

type    Constraints m = [Constraint m]
newtype Constraint  m = Constraint (m (), m Bool, String)

-- |A constraint is solvable if it knows how it can be solved in a certain
-- state (a monadic operation), if it can check afterwards whether the final
-- state satisfies it, and when it can be shown.
class (Show c, Monad m) => Solvable c m where 
   solveConstraint :: c -> m ()
   checkCondition  :: c -> m Bool
   
   -- default definition
   checkCondition _ = return True
   
instance Show (Constraint m) where 
   show (Constraint (_, _, s)) = s

instance Monad m => Solvable (Constraint m) m where
   solveConstraint (Constraint (f, _, _)) = f
   checkCondition  (Constraint (_, f, _)) = f

-- |Lifting a constraint to the Constraint data type. Every instance of
-- the Solvable type class can be lifted.
liftConstraint :: Solvable c m => c -> Constraint m
liftConstraint c = 
   Constraint (solveConstraint c, checkCondition c, show c)

liftConstraints :: Solvable c m => [c] -> Constraints m
liftConstraints = map liftConstraint

-- |If both constraints of type 'a' and 'b' can be solved in a Monad 'm', then
-- 'Either a b' constraints can also be solved in this monad.
instance (Solvable a m, Solvable b m) => Solvable (Either a b) m where
   solveConstraint = either solveConstraint solveConstraint
   checkCondition  = either checkCondition  checkCondition

-- |The data type ConstraintSum is similar to the (standard) Either data type.    
-- However, its Show instance is slightly different as the name of the constructor
-- is not shown.
data ConstraintSum f g info 
   = SumLeft  (f info) 
   | SumRight (g info)

instance (Show (f info), Show (g info)) => Show (ConstraintSum f g info) where
   show = constraintSum show show

instance (Functor f, Functor g) => Functor (ConstraintSum f g) where
   fmap f = constraintSum (SumLeft . fmap f) (SumRight . fmap f)

instance (Substitutable (f info), Substitutable (g info)) => Substitutable (ConstraintSum f g info) where
   (|->) sub = constraintSum (SumLeft . (sub |->)) (SumRight . (sub |->))
   ftv       = constraintSum ftv ftv

instance (Solvable (f info) m, Solvable (g info) m) => Solvable (ConstraintSum f g info) m where
   solveConstraint = constraintSum solveConstraint solveConstraint
   checkCondition  = constraintSum checkCondition  checkCondition

-- |Similar to the 'either' function.
constraintSum :: (f info -> c) -> (g info -> c) -> ConstraintSum f g info -> c
constraintSum f _ (SumLeft a)  = f a
constraintSum _ f (SumRight b) = f b