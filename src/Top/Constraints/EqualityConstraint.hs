-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Constraints.EqualityConstraint where

import Top.Types
import Top.Constraints.Constraints
import Top.States.TIState
import Top.States.SubstState
import Data.List (union)

data EqualityConstraint info = Equality Tp Tp info

-- constructor
(.==.) :: Solvable (EqualityConstraint info) m => Tp -> Tp -> info -> Constraint m
(t1 .==. t2) info = liftConstraint (Equality t1 t2 info)

instance Show info => Show (EqualityConstraint info) where
   show (Equality t1 t2 info) =
      show t1++" == "++show t2++"   : {"++show info++"}"
      
instance Substitutable (EqualityConstraint info) where

   sub |-> (Equality t1 t2 info) =
      Equality (sub |-> t1) (sub |-> t2) info
      
   ftv (Equality t1 t2 _) = 
      ftv t1 `union` ftv t2            
      
instance (Show info, HasSubst m info, HasTI m info) 
            => Solvable (EqualityConstraint info) m where

   solveConstraint (Equality t1 t2 info) = 
      unifyTerms info t1 t2
      
   checkCondition (Equality t1 t2 _) =
      do t1' <- applySubst t1
         t2' <- applySubst t2 
         (_ ,syns) <- getTypeSynonyms         
         return (expandType syns t1' == expandType syns t2')
