-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.ComposedSolvers.ChunkySolver where

import Top.Types
import Top.Solvers.SolveConstraints
import Top.ComposedSolvers.Tree
import Data.List (partition)

type ChunkConstraints constraint = (Chunks constraint, Dependencies constraint)
type Chunks           constraint = [Chunk constraint]
type Chunk            constraint = (ChunkID, Tree constraint)
type Dependency       constraint = (ChunkID, ChunkID, FixpointSubstitution -> Predicates -> constraint)
type Dependencies     constraint = [Dependency constraint]
type ChunkID                     = Int

solveChunkConstraints :: Solver constraint info -> (Tree constraint -> [constraint]) -> OrderedTypeSynonyms -> Int -> 
                            ChunkConstraints constraint -> SolveResult info
solveChunkConstraints solver flattening synonyms unique =  
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
