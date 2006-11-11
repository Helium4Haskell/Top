{-# OPTIONS -fglasgow-exts #-}

module Top.SolverET
   ( module Top.Solver  
   , solveConstraints 
   , solveResult
   ) where

import Top.Solver hiding (solveConstraints, solveResult)
import qualified Top.Solver as ORIGINAL (solveConstraints, solveResult)

import Top.ErrorTree (HasErrorTree, getErrorTreeEvaluator)
import Top.Util.Option
import Top.Interface.Basic

-- Import typeclasses 
import Top.Interface.Substitution  (HasSubst)
import Top.Interface.TypeInference (HasTI)
import Top.Interface.Qualification (HasQual)
import Top.Implementation.General  (SolveState)
import Top.Constraint              (Solvable)
import Top.Constraint.Information  (TypeConstraintInfo)
import Control.Monad.State         (MonadState)

--------------------------------------------------------------------------------
-- Define modified versions of the constraint solving operations, which optionally
-- post-processes the result of the solver to evaluate deferred error trees.

solveConstraints :: 
   ( HasTI m info
   , HasBasic m info
   , HasSubst m info
   , HasQual m info
   , TypeConstraintInfo info
   , HasErrorTree info
   , Solvable constraint m
   , MonadState s m
   , SolveState s
   , MonadWriter LogEntries m
   ) =>
     SolveOptions ->
     [constraint] -> 
     m (SolveResult info)
solveConstraints options cs =  ORIGINAL.solveConstraints options cs >>=
                               optionallyEvaluateDeferredErrorTrees


solveResult :: 
   ( HasBasic m info
   , HasTI m info
   , HasSubst m info
   , HasQual m info
   , TypeConstraintInfo info
   , HasErrorTree info
   ) => 
     m (SolveResult info)
solveResult = ORIGINAL.solveResult >>=
              optionallyEvaluateDeferredErrorTrees
 

--------------------------------------------------------------------------------
-- evaluate the error trees only if the appropriate option is set.

optionallyEvaluateDeferredErrorTrees :: ( HasSubst m info
                                        , HasTI m info
                                        , HasBasic m info
                                        , HasErrorTree info
                                        )
                                        => SolveResult info -> m (SolveResult info)
optionallyEvaluateDeferredErrorTrees res =
    do defer <- getOption deferErrorTrees
       if defer then do evalET <- getErrorTreeEvaluator
                        let newerrs = mapfst evalET (errorsFromResult res)
                        return (res {errorsFromResult = newerrs})
                else return res 

mapfst :: (a->b) -> [(a,c)] -> [(b,c)]
mapfst f = map (\(x,y) -> (f x, y))
