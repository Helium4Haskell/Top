{-# OPTIONS -fglasgow-exts -fallow-overlapping-instances  #-}

module Top.SolverET.Greedy
   ( module Top.Solver.Greedy
   , solveGreedy
   , greedyConstraintSolver
   , solveSimple
   , greedySimpleConstraintSolver
   ) where

import Top.Solver.Greedy hiding (solveGreedy, greedyConstraintSolver,
                                 solveSimple, greedySimpleConstraintSolver)
import Top.SolverET
import Top.ErrorTree 

-- Typeclasses 
import Top.Constraint              (Solvable)
import Top.Constraint.Information  (TypeConstraintInfo)

----------------------------------------------------------------------------------------------------
-- almost exact cut-and-paste from Top.Solver.Greedy, but with (HasErrorTree info) added to the
-- class context for all functions, and importing a modified Top.SolverET.solveConstraints

solveGreedy :: (Solvable constraint (Greedy info), TypeConstraintInfo info, HasErrorTree info) =>
               SolveOptions -> [constraint] -> Greedy info (SolveResult info)
solveGreedy = solveConstraints

greedyConstraintSolver :: (Solvable constraint (Greedy info), TypeConstraintInfo info, HasErrorTree info) =>
                          ConstraintSolver constraint info
greedyConstraintSolver = makeConstraintSolver solveGreedy

----------------------------------------------------------------------------------------------------

solveSimple :: (Solvable constraint (GreedySimple info), TypeConstraintInfo info, HasErrorTree info) =>
               SolveOptions -> [constraint] -> GreedySimple info (SolveResult info)
solveSimple = solveConstraints

greedySimpleConstraintSolver :: (Solvable constraint (GreedySimple info)
                                , TypeConstraintInfo info
                                , HasErrorTree info
                                )=>
                                ConstraintSolver constraint info
greedySimpleConstraintSolver = makeConstraintSolver solveSimple
