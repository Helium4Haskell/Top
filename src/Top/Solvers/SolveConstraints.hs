-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.Solvers.SolveConstraints where

import Top.Types
import Top.Constraints.Constraints
import Top.States.SubstState
import Top.States.BasicState
import Top.States.TIState
import Top.States.BasicMonad

type SolveX info sub ext = BasicX info (TIState info, (sub, ext))
type Solve  info sub     = SolveX info sub ()

instance HasTI (SolveX info sub ext) info where
   tiGet   = do (x,_) <- getX; return x
   tiPut x = do (_,y) <- getX; putX (x,y)

instance IsState (TIState info) where
   empty = emptyTI

solveConstraints :: ( IsState sub
                    , IsState ext
                    , HasSubst (SolveX info sub ext) info
                    , Solvable constraint (SolveX info sub ext)
                    ) 
                 => SolveX info sub ext ()              -- doFirst
                 -> SolveX info sub ext result          -- doAtEnd
                 -> OrderedTypeSynonyms                 -- synonyms
                 -> Int                                 -- unique
                 -> [constraint]                        -- constraints
                 -> SolveX info sub ext result          -- result
solveConstraints doFirst doAtEnd synonyms unique constraints = 
   do setUnique unique
      setTypeSynonyms synonyms 
      doFirst   
      pushConstraints (liftConstraints constraints)
      printState
      startSolving
      makeConsistent
      checkErrors
      doAtEnd

skip :: Monad m => m ()
skip = return ()

solveResult :: (HasBasic m info, HasTI m info, HasSubst m info) => m (SolveResult info)
solveResult = 
   do uniqueAtEnd <- getUnique
      errors      <- getErrors
      sub         <- fixpointSubst
      predicates  <- getPredicates     
      messages    <- getMessages
      return (SolveResult uniqueAtEnd sub (map fst predicates) errors messages)

-----------------------------------------------------------------------
-- Solve type constraints

type Solver constraint info = OrderedTypeSynonyms -> Int -> [constraint] -> SolveResult info

data SolveResult info = 
   SolveResult { uniqueFromResult       :: Int
               , substitutionFromResult :: FixpointSubstitution
               , predictesFromResult    :: Predicates
               , errorsFromResult       :: [info]
               , debugFromResult        :: String
               }

emptyResult :: Int -> SolveResult info
emptyResult i = SolveResult i emptyFPS [] [] []

combineResults :: SolveResult info -> SolveResult info -> SolveResult info
combineResults (SolveResult _ s1 ps1 er1 io1) (SolveResult unique s2 ps2 er2 io2) = 
   SolveResult unique (disjointFPS s1 s2) (ps1++ps2) (er1++er2) (io1++io2) 
   
---------------------------------------------------------------------
-- reduction of predicates

reducePredicates :: (HasSubst m info, HasBasic m info, HasTI m info) => m ()
reducePredicates = 
   do synonyms    <- getTypeSynonyms
      predicates  <- getPredicates
      substituted <- let f (predicate, info) = 
                              do predicate' <- applySubst predicate
                                 return (predicate', info)
                     in mapM f predicates
      let (reduced, errors) = associatedContextReduction synonyms standardClasses substituted
      mapM_ addError [ info | ReductionError (p, info) <- errors ]
      setPredicates reduced
