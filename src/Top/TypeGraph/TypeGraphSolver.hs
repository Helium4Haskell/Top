-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphSolver
   ( TypeGraph, TypeGraphX, TypeGraphState
   , runTypeGraph, runTypeGraphPlusDoAtEnd, solveTypeGraph
   ) where

import Top.TypeGraph.TypeGraphMonad
import Top.TypeGraph.TypeGraphSubst
import Top.TypeGraph.TypeGraphState
import qualified Top.TypeGraph.Implementation as Impl
import Top.Solvers.SolveConstraints
import Top.Solvers.BasicMonad
import Top.States.TIState
import Top.States.SubstState
import Top.States.States
import Top.Constraints.Constraints
import Top.Qualifiers.Qualifiers
import Top.Types
import Control.Monad
import Top.TypeGraph.Heuristics

type TypeGraphX info qs ext = SolveX info qs (TypeGraphState info) ext
type TypeGraph  info qs     = TypeGraphX info qs ()
 
instance HasTG (TypeGraphX info qs ext) info where
  tgGet   = do (_,(_,(z,_))) <- getX; return z
  tgPut z = do (x,(y,(_,w))) <- getX; putX (x,(y,(z,w)))
            
instance HasSubst (TypeGraphX info qs ext) info where
   substState = typegraphImpl
   
-----------------------------------------------------------------------------

instance HasTypeGraph (TypeGraphX info qs ext) info where
   addTermGraph            = lift1 Impl.addTermGraph
   addVertex               = lift2 Impl.addVertex
   addEdge                 = lift2 Impl.addEdge
   deleteEdge              = lift1 Impl.deleteEdge
   verticesInGroupOf       = lift1 Impl.verticesInGroupOf
   substituteTypeSafe      = lift1 Impl.substituteTypeSafe
   edgesFrom               = lift1 Impl.edgesFrom
   allPathsListWithout     = lift3 Impl.allPathsListWithout
   removeInconsistencies   = lift0 Impl.removeInconsistencies
   makeSubstitution        = lift0 Impl.makeSubstitution
   typeFromTermGraph       = lift1 Impl.typeFromTermGraph  
   markAsPossibleError     = lift1 Impl.markAsPossibleError
   getMarkedPossibleErrors = lift0 Impl.getMarkedPossibleErrors
   unmarkPossibleErrors    = lift0 Impl.unmarkPossibleErrors

lift0 f       = Impl.fromTypeGraph f 
lift1 f x     = Impl.fromTypeGraph $ f x 
lift2 f x y   = Impl.fromTypeGraph $ f x y
lift3 f x y z = Impl.fromTypeGraph $ f x y z

solveTypeGraph :: 
   ( IsState ext
   , Solvable constraint (TypeGraphX info qs ext)
   , QualifierList (TypeGraphX info qs ext) info qs qsInfo
   ) => 
     [Heuristic info] -> TypeGraphX info qs ext () ->
     ClassEnvironment -> OrderedTypeSynonyms -> Int -> [constraint] ->
     TypeGraphX info qs ext (SolveResult info qs ext)
     
solveTypeGraph hs todo classEnv syns unique = 
   solveConstraints doFirst doAtEnd
      where
         doFirst = 
            do setUnique unique
               setTypeSynonyms syns
               setClassEnvironment classEnv
               setHeuristics hs
         doAtEnd =
            do todo
               solveResult
               
{-runTypeGraphPlusDoAtEnd :: 
   ( IsState ext
   , Solvable constraint (TypeGraphX info qs ext)
   , QualifierList (TypeGraphX info qs ext) info qs qsInfo
   ) => 
     [Heuristic info] -> TypeGraphX info qs ext () -> SolverX constraint info qs ext
     -}
runTypeGraphPlusDoAtEnd hs todo classEnv syns unique = 
   eval . solveTypeGraph hs todo classEnv syns unique
{-   
runTypeGraph:: 
   ( IsState ext
   , Solvable constraint (TypeGraphX info qs ext)
   , QualifierList (TypeGraphX info qs ext) info qs qsInfo
   ) => 
     [Heuristic info] -> SolverX constraint info qs ext -}

runTypeGraph hs = 
   runTypeGraphPlusDoAtEnd hs (return ())
