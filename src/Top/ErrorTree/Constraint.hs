{-# OPTIONS -fglasgow-exts #-}
module Top.ErrorTree.Constraint
     ( ErrorTreeEqualityConstraint(..)
     , getErrorTreeEvaluator 
     ) where

import Top.ErrorTree.Interface
import Top.ErrorTree.ErrorTree

import Top.Types
import Top.Constraint
import Top.Constraint.Equality
import Top.Constraint.Information
import Top.Interface.Substitution
import Top.Interface.TypeInference
import Top.Interface.Basic
import Top.Util.Option
import Data.List(union)

-- TODO:
--  naming: evaluateErrorTree vs evalErrorTree vs evalET,
--          ErrorTreeEqualityConstraint vs ErrorTreeEqConstraint vs ETConstraint
--
--  question: is it a good or a bad idea to have the class constraint on the datatype??
--  e.g.: data HasErrorTree info => ErrorTreeEqualityConstraint info
--                                  = ErrorTreeEq (EqualityConstraint info)

---------------------------------------------------------------------------------------------------
-- ErrorTreeEqualityConstraint : new constraint type for equality constraints with an error tree.
-- instances for Show, Functor, Subsitutable and Solvable
-- solving an ErrorTreeEqualityConstraint

data ErrorTreeEqualityConstraint info
     = ErrorTreeEq (EqualityConstraint info)

instance (HasErrorTree info, Show info) => Show (ErrorTreeEqualityConstraint info) where
   show (ErrorTreeEq (Equality t1 t2 info)) = show t1 ++ " == " ++ show t2 ++ " : " ++ showinfo
        where showinfo | hasErrorTree info = "<Error Tree>\n" ++ show info
                       | otherwise         = "<Evaluated Error Tree> {" ++ show info ++ "}"
      
instance Functor ErrorTreeEqualityConstraint where
   fmap f (ErrorTreeEq c) = ErrorTreeEq (fmap f c)


instance HasErrorTree info => Substitutable (ErrorTreeEqualityConstraint info) where
   s |-> (ErrorTreeEq c) = ErrorTreeEq (subst c)
         where subst = (s |->) . (fmap (etsubst s))
               etsubst s i | hasErrorTree i = modifyErrorTree (s|->) i
                           | otherwise      = i

   ftv (ErrorTreeEq c@(Equality t1 t2 i)) = ftv c `union` etftv i
         where etftv i | hasErrorTree i = applyToErrorTree ftv i
                       | otherwise      = []
   

instance ( TypeConstraintInfo info 
         , HasErrorTree info
         , HasSubst m info
         , HasTI m info
         , HasBasic m info
         )
         => Solvable (ErrorTreeEqualityConstraint info) m
   where
      solveConstraint (ErrorTreeEq (Equality t1 t2 i)) = solveErrorTreeEqualityConstraint t1 t2 i 
      checkCondition (ErrorTreeEq c)                   = checkCondition c 


solveErrorTreeEqualityConstraint :: ( TypeConstraintInfo info 
                                    , HasErrorTree info
                                    , HasSubst m info
                                    , HasTI m info
                                    , HasBasic m info
                                    )
                                    => Tp -> Tp -> info -> m ()
solveErrorTreeEqualityConstraint t1 t2 info = 
    do defer <- getOption deferErrorTrees
       if (not defer) && (hasErrorTree info) 
          then do evalET <- getErrorTreeEvaluator
                  unifyTerms (equalityTypePair (t1, t2) (evalET info)) t1 t2
          else unifyTerms (equalityTypePair (t1, t2) info) t1 t2


getErrorTreeEvaluator :: ( HasErrorTree info
                         , HasSubst m info
                         , HasTI m info
                         , HasBasic m info
                         )
                         => m (info -> info) 
getErrorTreeEvaluator = do sub      <- fixpointSubst
                           (_,syns) <- getTypeSynonyms        
                           let ordsyns   = (fst (getTypeSynonymOrdering syns), syns)
                           let evaluator i | hasErrorTree i = evalErrorTree (evaluateErrorTree ordsyns sub) i
                                           | otherwise      = i
                           return evaluator
