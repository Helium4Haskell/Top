-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.ComposedSolvers.ChunkySolver where

import Top.Types
import Top.Constraints.Constraints
import Top.Solvers.GreedySolver (Greedy, solveGreedy)
import Top.Solvers.SolveConstraints
import Top.TypeGraph.TypeGraphSolver (TypeGraph, solveTypeGraph)
import Top.TypeGraph.Heuristics
import Top.ComposedSolvers.CombinationSolver (solveCombination)
import Top.ComposedSolvers.Tree
import Data.List (partition)
import Data.FiniteMap
import Utils (internalError)

type ChunkConstraints constraint = (Chunks constraint, Dependencies constraint)
type Chunks           constraint = [Chunk constraint]
type Chunk            constraint = (ChunkID, Tree constraint)
type Dependency       constraint = (ChunkID, ChunkID, FixpointSubstitution -> Predicates -> constraint)
type Dependencies     constraint = [Dependency constraint]
type ChunkID                     = Int

singletonChunk :: [constraint] -> ChunkConstraints constraint
singletonChunk cs = ([(0, listTree cs)], [])

solveChunkConstraints :: ( Solvable constraint (Greedy info)
                         , Solvable constraint (TypeGraph info)
                         , Show info
                         ) => [Heuristic info] -> (Tree constraint -> [constraint]) -> OrderedTypeSynonyms -> Int -> ChunkConstraints constraint -> SolveResult info
solveChunkConstraints hs = 
   solveChunky (solveCombination hs) 
   
solveChunky solver flattening synonyms unique =  
   rec unique . insertDependencies (< 0) emptyFPS []

   where 
      rec unique (chunks, dependencies) =
         case chunks of 
            [] -> emptyResult unique
            (chunkID, constraintTree) : otherChunks -> 
               let constraintList = flattening constraintTree
                   result@(SolveResult unique' sub preds _ _)
                      | null constraintList = emptyResult unique
                      | otherwise           = solver synonyms unique constraintList
                   nextChunkConstraints     = insertDependencies (==chunkID) sub preds (otherChunks, dependencies)
               in combineResults result (rec unique' nextChunkConstraints)
    
      insertDependencies :: (ChunkID -> Bool) -> FixpointSubstitution -> Predicates -> ChunkConstraints constraint -> ChunkConstraints constraint
      insertDependencies condition substitution predicates (chunks, dependencies) = 
         let (toInsert, otherDependencies) = partition (\(x,_,_) -> condition x) dependencies
             insertOne (_, cid, cfun) = 
                let rec [] = [(cid, unitTree (cfun substitution predicates))]
                    rec (tuple@(cid', cs):rest)
                       | cid == cid' = (cid, [cfun substitution predicates] .>>. cs) : rest
                       | otherwise   = tuple : rec rest
                in rec 
         in (foldr insertOne chunks toInsert, otherDependencies)
