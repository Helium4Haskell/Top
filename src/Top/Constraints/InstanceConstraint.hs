-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Constraints.InstanceConstraint where

import Top.Types
import Top.Constraints.Constraints
import Top.Constraints.EqualityConstraint
import Top.Constraints.PredicateConstraint
import Top.States.TIState
import Top.States.BasicState
import Top.States.SubstState
import Data.List (union)

data InstanceConstraint info
   = ExplicitInstance Tp TpScheme  ((Tp,Tp) -> info {- to equality -}, Predicate -> info -> info {- to predicates -})
   | ImplicitInstance Tp Tps Tp    ((Tp,Tp) -> info {- to equality -}, Predicate -> info -> info {- to predicates -})
   
-- constructors
(.::.) :: Solvable (InstanceConstraint info) m => Tp -> TpScheme -> ((Tp,Tp) -> info, Predicate -> info -> info) -> Constraint m
(tp .::. ts) (f1, f2) = liftConstraint (ExplicitInstance tp ts (f1, f2))

(.<=.) :: Solvable (InstanceConstraint info) m => Tp -> (Tps, Tp) -> ((Tp,Tp) -> info) -> Constraint m
(t1 .<=. (ms,t2)) infoF = liftConstraint (ImplicitInstance t1 ms t2 (infoF, const id))

instance Show info => Show (InstanceConstraint info) where
   show (ExplicitInstance tp ts (infoF,_)) =
      let unknowns = (TCon "?",TCon "?")
      in show tp++" :: "++show ts++"   : {"++show (infoF unknowns)++"}"
   show (ImplicitInstance t1 ms t2 (infoF,_)) =
      let unknowns = (TCon "?",TCon "?")
          monos    = if null ms then "" else "monos="++show (ftv ms)++"; "
      in show t1++" <= ("++monos++show t2++")   : {"++show (infoF unknowns)++"}"
      
instance Substitutable (InstanceConstraint info) where

   sub |-> (ImplicitInstance t1 monos t2 tuple) =
      ImplicitInstance (sub |-> t1) (sub |-> monos) (sub |-> t2) tuple
   sub |-> (ExplicitInstance tp ts tuple) =
      ExplicitInstance (sub |-> tp) (sub |-> ts) tuple
                           
   ftv (ImplicitInstance t1 monos t2 _) =
      ftv t1 `union` ftv monos `union` ftv t2
   ftv (ExplicitInstance tp ts _) =
      ftv tp `union` ftv ts  
           
instance (Show info, HasBasic m info, HasTI m info, HasSubst m info) 
            => Solvable (InstanceConstraint info) m where

   solveConstraint (ExplicitInstance tp ts (f1, f2)) =            
      do unique <- getUnique
         let (unique', qtype) = instantiate unique ts
             (ps,its) = split qtype
             info     = f1 (its,tp)
         setUnique unique'              
         pushConstraint  (tp .==. its $ info)
         pushConstraints (map (\p -> predicate p (f2 p info)) ps)

   solveConstraint (ImplicitInstance t1 ms t2 (f1,f2)) =
      do makeConsistent
         t2' <- applySubst t2
         ms' <- mapM applySubst ms
         ps  <- getPredicates
         let scheme = makeScheme (ftv ms') (map fst ps) t2'
         pushConstraint (t1 .::. scheme $ (f1,f2))
