-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.GreedySolver (Greedy, GreedyX, GreedyState, solveGreedy, runGreedyPlusDoAtEnd, runGreedy) where

import Top.Solvers.SolveConstraints
import Top.Solvers.GreedySubst
import Top.Solvers.BasicMonad
import Top.States.TIState
import Top.States.SubstState
import Top.States.States
import Top.Types
import Top.Constraints.Constraints
import Top.Constraints.TypeConstraintInfo
import Top.Qualifiers.Qualifiers

import Data.FiniteMap

type GreedyX info qs ext = SolveX info qs GreedyState ext
type Greedy  info qs     = GreedyX info qs ()

solveGreedy :: 
   ( IsState ext
   , Solvable constraint (GreedyX info qs ext)
   , QualifierList (GreedyX info qs ext) info qs qsInfo
   ) => 
     GreedyX info qs ext () ->
     ClassEnvironment -> OrderedTypeSynonyms -> Int -> [constraint] ->
     GreedyX info qs ext (SolveResult info qs ext)

solveGreedy todo classEnv syns unique = 
   solveConstraints doFirst doAtEnd
      where
         doFirst = 
            do setUnique unique
               setTypeSynonyms syns
               setClassEnvironment classEnv
         doAtEnd =
            do todo
               solveResult

runGreedyPlusDoAtEnd todo classEnv syns unique = 
   eval . solveGreedy todo classEnv syns unique

runGreedy x = 
   runGreedyPlusDoAtEnd (return ()) x

instance HasSubst (GreedyX info qs ext) info where
   substState = greedyState

instance HasGreedy (GreedyX info qs ext) info where
   greedyGet   = do (_,(_,(z,_))) <- getX; return z
   greedyPut z = do (x,(y,(_,w))) <- getX; putX (x,(y,(z,w)))
