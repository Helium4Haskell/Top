-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.ComposedSolvers.CombinationSolver (solveCombination) where

import Top.ComposedSolvers.Tree
import Top.Solvers.GreedySolver (Greedy, solveGreedy)
import Top.TypeGraph.TypeGraphSolver (TypeGraph, solveTypeGraph)
import Top.Solvers.SolveConstraints
import Top.Constraints.Constraints
import Top.Types
import Top.TypeGraph.Heuristics

solveCombination :: ( Solvable constraint (Greedy info)
                    , Solvable constraint (TypeGraph info)
                    , Show info
                    ) => [Heuristic info] -> Solver constraint info
solveCombination hs =
   solveGreedy |>>| solveTypeGraph hs

-- |The first solver is used to solve the constraint set. If this fails (at least one 
-- error is returned), then the second solver takes over.     
(|>>|) :: Solver constraint info -> Solver constraint info -> Solver constraint info
s1 |>>| s2 = \synonyms unique constraints -> 
   let r1 = s1 synonyms unique constraints
       r2 = s2 synonyms unique constraints
   in if null (errorsFromResult r1) then r1 else r2
