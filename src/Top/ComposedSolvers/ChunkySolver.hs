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
          newRest   = [ (chunkID, fmap (update schemeMap) t) | (chunkID, t) <- rest ]
      in result `plus` (rec newUnique newRest)