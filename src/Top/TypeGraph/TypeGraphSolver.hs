-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.TypeGraphSolver (TypeGraph, TypeGraphX, evalTypeGraph, TypeGraphState, solveTypeGraph) where

import Top.TypeGraph.TypeGraphMonad
import Top.TypeGraph.TypeGraphSubst
import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.ApplyHeuristics
import Top.TypeGraph.Paths
import Top.TypeGraph.Basics
import Top.Solvers.SolveConstraints
import Top.States.BasicMonad
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.Constraints.Constraints
import Top.Types
import Data.FiniteMap
import Control.Monad
import Top.TypeGraph.Heuristics

type TypeGraphX info ext = SolveX info (TypeGraphState info) ext
type TypeGraph  info     = TypeGraphX info ()

evalTypeGraph :: Show info => TypeGraph info a -> a  
evalTypeGraph = eval

solveTypeGraph :: (Show info, Solvable constraint (TypeGraph info))  
                     => [Heuristic info] -> Solver constraint info
solveTypeGraph hs synonyms unique = 
   evalTypeGraph . solveConstraints (setHeuristics hs) solveResult synonyms unique

instance Show info => IsState (TypeGraphState info) where
   empty = emptyTypeGraph 

instance HasTG (TypeGraphX info ext) info where
  tgGet   = do (_,(y,_)) <- getX; return y
  tgPut y = do (x,(_,z)) <- getX; putX (x,(y,z))
            
instance HasSubst (TypeGraphX info ext) info where
   substState = typegraphImpl
   
-----------------------------------------------------------------------------

instance HasTypeGraph (TypeGraphX info ext) info where

   addVertex i info =
      debugTrace ("addVertex " ++ show i) >>
      createNewGroup (insertVertex i info emptyGroup)

   allVariables = 
      debugTrace "allVariables" >>
      tgGets (keysFM . referenceMap)     
    
   makeSubstitution =
      do synonyms <- getTypeSynonyms
         eqgroups <- tgGets (eltsFM . equivalenceGroupMap) 
         let f eqc = [ (v, tp) | let tp = typeOfGroup synonyms eqc,  (v,_) <- vertices eqc, notId v tp ]
             notId i (TVar j) = i /= j
             notId _ _        = True
         return (concatMap f eqgroups)
         
   -- add an edge and propagate equality
   addEdge edge@(EdgeID v1 v2) info =
      debugTrace ("addEdge " ++ show edge) >>      
      do propagateEquality [v1,v2] 
         combineClasses v1 v2
         cnr <- nextConstraintNumber
         updateEquivalenceGroupOf v1 (insertEdge edge cnr info)

   addClique clique@(cnr,lists) = 
      debugTrace ("addClique " ++ show clique) >>
      do case filter (not . null) lists of
           []                -> return ()
           ((v1,_):_) : rest -> 
              do mapM_ (combineClasses v1) (map (fst . head) rest)
                 updateEquivalenceGroupOf v1 (combineCliques clique)

   verticesInGroupOf i =
      debugTrace ("verticesInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (vertices eqc)

   constantsInGroupOf i =
      debugTrace ("constantsInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (constants eqc)     

   edgesInGroupOf i =
      debugTrace ("edgesInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (edges eqc)    
   
   representativeInGroupOf i =
      debugTrace ("representativeInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (representative eqc)   

   deleteEdge edge@(EdgeID v1 v2) =
      debugTrace ("deleteEdge "++show edge) >>
      do eqgroup <- equivalenceGroupOf v1
         removeGroup eqgroup
         let newGroups = splitGroup (removeEdge edge eqgroup)
         mapM_ createNewGroup newGroups
         let is = map representative newGroups
         cliques <- lookForCliques is                   
         mapM_ deleteClique cliques         

   deleteClique clique =
      debugTrace ("deleteClique " ++ show clique) >>
      do let vid = fst . head . head . snd $ clique 
         eqgroup <- equivalenceGroupOf vid
         removeGroup eqgroup
         let newGroups = splitGroup (removeClique clique eqgroup)
         mapM_ createNewGroup newGroups
         let is = map representative newGroups
         cliques <- lookForCliques is
         mapM_ deleteClique cliques
            
   extractPossibleErrors = 
      debugTrace "getConflicts" >>
      do errors <- getPossibleErrors
         setPossibleErrors []
         return errors     
                     
   useHeuristics = 
      debugTrace "applyHeuristics" >> 
      do hs <- tgGets typegraphHeuristics
         (edges, errors) <- applyHeuristics hs
         mapM_ deleteEdge edges
         mapM_ addError errors                                                                

   allPathsList = allPathsListWithout []
   
   allPathsListWithout without v1 vs = 
      debugTrace ("allPathsList' "++show v1++" "++show vs) >>
      do eqc <- equivalenceGroupOf v1
         rec [] (pathsFrom v1 vs eqc) where 
   
      rec history path = 
         let f (EdgeID v1 v2, Implied cnr p1 p2) = 
                do eqc <- equivalenceGroupOf p1
                   parentspaths <- if (p1,p2) `elem` history
                                     then return Empty
                                     else rec ((p1,p2):history) (pathsFromWithout without p1 [p2] eqc)
                   return $ Step (EdgeID p1 v1,Child cnr)
                            :+: parentspaths
                            :+: Step (EdgeID p2 v2,Child cnr)                                     
             f tuple  = return (Step tuple)
         in return path
            
   -- a non-recursive function to find a type for a type variable:
   --   if the type is an application (of two children), then these 
   --   are not substituted into the type that they represent
   substForVar_nr = \i ->      
        debugTrace ("substForVar_nr " ++ show i) >>
        do synonyms   <- getTypeSynonyms
           eqgroup <- equivalenceGroupOf i           
           return (typeOfGroup synonyms eqgroup)
