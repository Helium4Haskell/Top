-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Constraints.Constraints where

type    Constraints m = [Constraint m]
newtype Constraint  m = Constraint (m (), m Bool, String)

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

liftConstraint :: Solvable c m => c -> Constraint m
liftConstraint c = 
   Constraint (solveConstraint c, checkCondition c, show c)

liftConstraints :: Solvable c m => [c] -> Constraints m
liftConstraints = map liftConstraint
