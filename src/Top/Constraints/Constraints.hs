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
