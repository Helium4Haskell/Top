{-# OPTIONS -fglasgow-exts -fallow-overlapping-instances #-}

module Top.SolverET.TypeGraph
   ( module Top.Solver.TypeGraph
   , solveTypeGraph
   , typegraphConstraintSolver
   , typegraphConstraintSolverDefault
   ) where

import Top.Solver.TypeGraph hiding (solveTypeGraph,
                                    typegraphConstraintSolver,
                                    typegraphConstraintSolverDefault)
import Top.SolverET
import Top.ErrorTree

import Top.Monad.Select
import Top.Implementation.TypeGraphSubstitution
import Top.Implementation.TypeGraph.Heuristic

-- Typeclasses: 
import Top.Constraint              (Solvable)
import Top.Constraint.Information  (TypeConstraintInfo)

----------------------------------------------------------------------------------------------------
-- almost exact cut-and-paste from Top.Solver.TypeGraph, but with (HasErrorTree info) added to the
-- class context for all functions, and importing a modified Top.SolverET.solveResult

solveTypeGraph :: (Solvable constraint (TG info), TypeConstraintInfo info, HasErrorTree info)
                     => TG info () -> SolveOptions -> [constraint] -> TG info (SolveResult info)
solveTypeGraph m options cs =
   do initialize cs options >> m
      onlySolveConstraints cs
      solveResult

typegraphConstraintSolver :: (Solvable constraint (TG info), TypeConstraintInfo info, HasErrorTree info)
                                => PathHeuristics info -> ConstraintSolver constraint info
typegraphConstraintSolver hs = 
   let setHeuristics = deselect (modify (\tgs -> tgs { heuristics = hs }))
   in makeConstraintSolver (solveTypeGraph setHeuristics)

typegraphConstraintSolverDefault :: (Solvable constraint (TG info), TypeConstraintInfo info, HasErrorTree info)
                                       => ConstraintSolver constraint info
typegraphConstraintSolverDefault = 
   makeConstraintSolver (solveTypeGraph (return ()))
