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
import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.ApplyHeuristics
import Top.TypeGraph.Basics
import Top.Solvers.SolveConstraints
import Top.Solvers.BasicMonad
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.States.States
import Top.Constraints.Constraints
import Top.Qualifiers.Qualifiers
import Top.Types
import Data.FiniteMap
import qualified Data.Set as S
import Control.Monad
import Top.TypeGraph.Heuristics
import Utils (internalError)


type TypeGraphX info qs ext = SolveX info qs (TypeGraphState info) ext
type TypeGraph  info qs     = TypeGraphX info qs ()
{-
evalTypeGraph :: Show info => TypeGraph info a -> a  
evalTypeGraph = eval
   
solveTypeGraph :: (Show info, Solvable constraint (TypeGraph info), Zero ext)  
                     => [Heuristic info] -> SolverX constraint info ext
solveTypeGraph hs classEnv synonyms unique = 
   let doFirst = do setUnique unique
                    setTypeSynonyms synonyms
                    setClassEnvironment classEnv
                    setHeuristics hs                    
   in evalTypeGraph . solveConstraints doFirst solveResult

solveTypeGraphPlusDoAtEnd :: (Show info, Solvable constraint (TypeGraph info), Zero ext)  
                     => [Heuristic info] -> TypeGraph info () -> SolverX constraint info ext
solveTypeGraphPlusDoAtEnd hs doAtEnd classEnv synonyms unique = 
   let doFirst = do setUnique unique
                    setTypeSynonyms synonyms
                    setClassEnvironment classEnv
                    setHeuristics hs 
   in evalTypeGraph . solveConstraints doFirst (doAtEnd >> solveResult)
  -} 

instance HasTG (TypeGraphX info qs ext) info where
  tgGet   = do (_,(_,(z,_))) <- getX; return z
  tgPut z = do (x,(y,(_,w))) <- getX; putX (x,(y,(z,w)))
            
instance HasSubst (TypeGraphX info qs ext) info where
   substState = typegraphImpl
   
-----------------------------------------------------------------------------

instance HasTypeGraph (TypeGraphX info qs ext) info where

   addVertex i info =
      debugTrace ("addVertex " ++ show i) >>
      do createNewGroup (insertVertex i info emptyGroup)
         return ()
    
   makeSubstitution =
      debugTrace ("makeSubstitution") >>   
      do makeConsistent -- temp
         syns     <- getTypeSynonyms
         eqgroups <- tgGets (eltsFM . equivalenceGroupMap) 
         let f eqc = case typeOfGroup syns eqc of 
                        Nothing -> internalError "Top.TypeGraph.TypeGraphSolver" "makeSubstitution" "inconsistent state"
                        Just tp -> return [ (v, tp) | (v,_) <- vertices eqc, notId v tp ]
             notId i (TVar j) = i /= j
             notId _ _        = True
         res <- mapM f eqgroups
         return (concat res)
         
   -- add a new edge and propagate equality
   addNewEdge edge info =
      debugTrace ("addNewEdge " ++ show edge) >>      
      do cnr <- nextConstraintNumber
         addEdge edge (cnr, info)
         
   -- add an edge and propagate equality (but don't introduce a new constraint number)
   addEdge edge@(EdgeID v1 v2) (cnr, info) =
      debugTrace ("addEdge " ++ show edge) >>      
      do propagateEquality [v1,v2] 
         combineClasses v1 v2
         updateEquivalenceGroupOf v1 (insertEdge edge cnr info)
         
   addClique clique@(_, lists) = 
      debugTrace ("addClique " ++ show clique) >>
      do case filter (not . null) lists of
           []                -> return ()
           ((v1,_):_) : rest -> 
              do mapM_ (combineClasses v1) (map (fst . head) rest)
                 updateEquivalenceGroupOf v1 (combineCliques clique)
           _ -> internalError "Top.TypeGraph.TypeGraphSolver" "addClique" "unexpected clique list"

   verticesInGroupOf i =
      debugTrace ("verticesInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (vertices eqc)

   constantsInGroupOf i =
      debugTrace ("constantsInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (constants eqc)     
	 
   edgesFrom i =
      debugTrace ("edgesFrom " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         let predicate (EdgeID v1 v2,_,_) = v1 == i || v2 == i
         return (filter predicate (edges eqc))

   deleteEdge edge@(EdgeID v1 _) =
      debugTrace ("deleteEdge "++show edge) >>
      do eqgroup <- equivalenceGroupOf v1
         removeGroup eqgroup
         let newGroups = splitGroup (removeEdge edge eqgroup)
         is <- mapM createNewGroup newGroups
         cliques <- lookForCliques is                   
         mapM_ deleteClique cliques       

   deleteClique clique =
      debugTrace ("deleteClique " ++ show clique) >>
      do let vid = fst . head . head . snd $ clique 
         eqgroup <- equivalenceGroupOf vid
         removeGroup eqgroup
         let newGroups = splitGroup (removeClique clique eqgroup)
         is <- mapM createNewGroup newGroups
         cliques <- lookForCliques is
         mapM_ deleteClique cliques
            
   getPossibleInconsistentGroups = 
      debugTrace "getPossibleInconsistentGroups" >>
      getPossibleErrors
	 
   noPossibleInconsistentGroups = 
      debugTrace "setPossibleInconsistentGroups" >>
      setPossibleErrors []
	 
   removeInconsistencies = 
      debugTrace "removeInconsistencies" >> 
      do hs         <- tgGets typegraphHeuristics
         (es, errs) <- applyHeuristics hs
         mapM_ deleteEdge es
         mapM_ addError errs 
         if null errs && null es
	   then -- everything is okay: no errors were found.
	        noPossibleInconsistentGroups
           else -- Bug patch 3 february 2004
	        -- safety first: check whether *everything* is really removed. 
	        removeInconsistencies
	 
   allPathsList = allPathsListWithout S.emptySet
   
   allPathsListWithout without v1 vs =
      debugTrace ("allPathsList' "++show v1++" "++show vs) >>
      do eqc <- equivalenceGroupOf v1
         return (equalPaths without v1 vs eqc)
            
   -- a non-recursive function to find a type for a type variable:
   --   if the type is an application (of two children), then these 
   --   are not substituted into the type that they represent
   substForVar_nr = \i ->      
        debugTrace ("substForVar_nr " ++ show i) >>
        do syns    <- getTypeSynonyms
           eqgroup <- equivalenceGroupOf i
           case typeOfGroup syns eqgroup of
              Just result -> return result
              Nothing     -> internalError "Top.TypeGraph.TypeGraphSolver" "substForVar_nr" "inconsistent state"

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