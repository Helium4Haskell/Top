-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.ComposedSolvers.CombinationSolver where

import Top.Solvers.SolveConstraints
import Top.States.BasicState

-- |The first solver is used to solve the constraint set. If this fails (at least one 
-- error is returned), then the second solver takes over.     
(|>>|) :: SolverX constraint info qs ext -> SolverX constraint info qs ext -> SolverX constraint info qs ext
s1 |>>| s2 = \classEnv synonyms unique constraints -> 
   let r1 = s1 classEnv synonyms unique constraints
       r2 = s2 classEnv synonyms unique constraints
       p (_, ErrorLabel s) = s /= "ambiguous predicate" -- temporary*
       p _                 = True
   in if null (filter p $ errorsFromResult r1) then r1 else r2

-- * For now, ignore the ambiguous predicate messages that are returned. They are not shown anyway.
-- These error messages are returned because of the mismatch between the constraints that are generated
-- by the Helium compiler, and the constraints as they are in the Top constraint solver.