-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.SimpleSolver (Simple, SimpleX, evalSimple, SimpleState, solveSimple) where

import Top.States.BasicMonad
import Top.States.TIState
import Top.States.SubstState
import Top.Solvers.SolveConstraints
import Top.Solvers.SimpleSubst
import Top.Types
import Top.Constraints.Constraints

evalSimple :: Simple info a -> a
evalSimple = eval

type SimpleX info ext = SolveX info SimpleState ext
type Simple  info     = SimpleX info ()

solveSimple :: Solvable constraint (Simple info) 
                  => Solver constraint info
solveSimple synonyms unique = 
   evalSimple . solveConstraints skip solveResult synonyms unique

instance IsState SimpleState where
   empty     = emptySimple
  
instance HasSubst (SimpleX info ext) info where
   substState = simpleState

instance HasSimple (SimpleX info ext) info where
   simpleGet   = do (_,(y,_)) <- getX; return y
   simplePut y = do (x,(_,z)) <- getX; putX (x,(y,z))
