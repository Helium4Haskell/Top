-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.SimpleSolver (Simple, SimpleX, SimpleState, solveSimple, runSimplePlusDoAtEnd, runSimple) where

import Top.States.TIState
import Top.States.SubstState
import Top.States.States
import Top.Solvers.BasicMonad
import Top.Solvers.SolveConstraints
import Top.Solvers.SimpleSubst
import Top.Types
import Top.Constraints.Constraints
import Top.Constraints.TypeConstraintInfo
import Top.Qualifiers.Qualifiers

type SimpleX info qs ext = SolveX info qs SimpleState ext
type Simple  info qs     = SimpleX info qs ()

solveSimple :: 
   ( IsState ext
   , Solvable constraint (SimpleX info qs ext)
   , QualifierList (SimpleX info qs ext) info qs qsInfo
   ) => 
     SimpleX info qs ext () ->
     ClassEnvironment -> OrderedTypeSynonyms -> Int -> [constraint] ->
     SimpleX info qs ext (SolveResult info qs ext)

solveSimple todo classEnv syns unique = 
   solveConstraints doFirst doAtEnd
      where
         doFirst = 
            do setUnique unique
               setTypeSynonyms syns
               setClassEnvironment classEnv
         doAtEnd =
            do todo
               solveResult
   
runSimplePlusDoAtEnd todo classEnv syns unique = 
   eval . solveSimple todo classEnv syns unique

runSimple x = 
   runSimplePlusDoAtEnd (return ()) x
   
instance HasSubst (SimpleX info qs ext) info where
   substState = simpleState

instance HasSimple (SimpleX info qs ext) info where
   simpleGet   = do (_,(_,(z,_))) <- getX; return z
   simplePut z = do (x,(y,(_,w))) <- getX; putX (x,(y,(z,w)))
