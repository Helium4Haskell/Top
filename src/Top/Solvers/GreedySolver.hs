-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.GreedySolver (Greedy, GreedyX, evalGreedy, GreedyState, solveGreedy) where

import Top.Solvers.SolveConstraints
import Top.Solvers.GreedySubst
import Top.States.BasicMonad
import Top.States.TIState
import Top.States.SubstState
import Top.Types
import Top.Constraints.Constraints

type GreedyX info ext = SolveX info GreedyState ext
type Greedy  info     = GreedyX info ()

evalGreedy :: Greedy info a -> a
evalGreedy = eval

solveGreedy :: Solvable constraint (Greedy info) 
                  => Solver constraint info
solveGreedy synonyms unique = 
   evalGreedy . solveConstraints skip solveResult synonyms unique
   
instance IsState GreedyState where
   empty = emptyGreedy

instance HasSubst (GreedyX info ext) info where
   substState = greedyState

instance HasGreedy (GreedyX info ext) info where
   greedyGet   = do (_,(y,_)) <- getX; return y
   greedyPut y = do (x,(_,z)) <- getX; putX (x,(y,z))
