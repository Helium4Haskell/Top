-----------------------------------------------------------------------------
-- |                                   
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental      
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.ComposedSolvers.ChunkySolver where

import Top.Types
import Top.States.States
import Top.Solvers.SolveConstraints
import Top.ComposedSolvers.Tree
import Data.List (partition)
import Data.FiniteMap

type Chunks constraint = [Chunk constraint]
type Chunk  constraint = (ChunkID, Tree constraint)
type ChunkID           = Int

solveChunkConstraints :: (Empty ext, Plus ext) => 
   (FiniteMap Int (Scheme qs) -> constraint -> constraint) -> -- function to update the type scheme variables
   SolverX constraint info qs ext ->                          -- constraint solver to solve the constraints in a chunk
   (Tree constraint -> [constraint]) ->                       -- function to flatten the constraint tree
   ClassEnvironment -> OrderedTypeSynonyms -> 
   Int -> Chunks constraint -> SolveResult info qs ext
   
solveChunkConstraints update solver flattening classEnv synonyms = rec
   
 where
   rec unique [] = emptyResult unique
   rec unique ((_, tree) : rest) =
      let constraintList = flattening tree
          result
             | null constraintList = 
                  emptyResult unique
             | otherwise = 
                  solver classEnv synonyms unique constraintList
          newUnique = uniqueFromResult result
          schemeMap = typeschemesFromResult result
          newRest   = [ (chunkID, fmap (update schemeMap) tree) | (chunkID, tree) <- rest ]
      in result `plus` (rec newUnique newRest)

{-
type ChunkConstraints constraint = (Chunks constraint, Dependencies constraint)
type Chunks           constraint = [Chunk constraint]
type Chunk            constraint = (ChunkID, Tree constraint)
type Dependency       constraint = (ChunkID, ChunkID, FixpointSubstitution -> Predicates -> constraint)
type Dependencies     constraint = [Dependency constraint]
type ChunkID                     = Int

solveChunkConstraints :: (Empty ext, Plus ext) => SolverX constraint info qs ext -> (Tree constraint -> [constraint]) 
                            -> ClassEnvironment -> OrderedTypeSynonyms -> Int 
                            -> ChunkConstraints constraint -> SolveResult info qs ext
solveChunkConstraints solver flattening classEnv synonyms unique = 
   rec unique . insertDependencies (< 0) emptyFPS []

   where 
      rec unique (chunks, dependencies) =
         case chunks of 
            [] -> emptyResult unique
            (chunkID, constraintTree) : otherChunks -> 
               let constraintList = flattening constraintTree
                   result@(SolveResult unique' sub _ preds _ _ _) -- breaks abstraction
                      | null constraintList = emptyResult unique
                      | otherwise           = solver classEnv synonyms unique constraintList
                   nextChunkConstraints     = insertDependencies (==chunkID) sub preds (otherChunks, dependencies)
               in result `plus` (rec unique' nextChunkConstraints)

      insertDependencies :: (ChunkID -> Bool) -> FixpointSubstitution -> Predicates -> ChunkConstraints constraint -> ChunkConstraints constraint
      insertDependencies condition substitution predicates (chunks, dependencies) = 
         let (toInsert, otherDependencies) = partition (\(x,_,_) -> condition x) dependencies
             insertOne (_, cid, cfun) = 
                let rec [] = [(cid, unitTree (cfun substitution predicates))]
                    rec (tuple@(cid', cs):rest)
                       | cid == cid' = (cid, [cfun substitution predicates] .>>. cs) : rest
                       | otherwise   = tuple : rec rest
                in rec 
         in (foldr insertOne chunks toInsert, otherDependencies) -}