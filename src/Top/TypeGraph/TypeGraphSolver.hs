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
import Data.List
import Control.Monad
import Top.TypeGraph.Heuristics
import Utils (internalError)

type TypeGraphX info qs ext = SolveX info qs (TypeGraphState info) ext
type TypeGraph  info qs     = TypeGraphX info qs ()
 
instance HasTG (TypeGraphX info qs ext) info where
  tgGet   = do (_,(_,(z,_))) <- getX; return z
  tgPut z = do (x,(y,(_,w))) <- getX; putX (x,(y,(z,w)))
            
instance HasSubst (TypeGraphX info qs ext) info where
   substState = typegraphImpl
   
-----------------------------------------------------------------------------

instance HasTypeGraph (TypeGraphX info qs ext) info where

   addTermGraph tp =
      debugTrace ("addTermGraph " ++ show tp) >>
      do syns <- getTypeSynonyms
         let (newtp, original) = 
                case expandToplevelTC syns tp of
                   Nothing -> (tp, Nothing) 
                   Just x  -> (x, Just tp)
         case newtp of
            TVar i     -> return i
            TCon s     -> makeNewVertex (VCon s, original)
            TApp t1 t2 -> 
               do v1 <- addTermGraph t1
                  v2 <- addTermGraph t2
                  makeNewVertex (VApp v1 v2, original)
   
   addVertex i info =
      do createNewGroup (insertVertex i info emptyGroup)
         return ()

   substituteVariable i =
      do syns    <- getTypeSynonyms
         eqgroup <- equivalenceGroupOf i
         case typeOfGroup syns eqgroup of
            Just tp -> 
               case tp of 
                  TVar _ -> return tp
                  _ -> 
                     let rec (TVar j)   = substituteVariable j
                         rec t@(TCon _) = return t
                         rec (TApp l r) = 
                            do l' <- rec l
                               r' <- rec r
                               return (TApp l' r')
                     in rec tp
            Nothing -> internalError "Top.TypeGraph.TypeGraphSolver" "substituteVariable" "inconsistent state"
    
   makeSubstitution =
      debugTrace ("makeSubstitution") >>
      do syns     <- getTypeSynonyms
         eqgroups <- tgGets (eltsFM . equivalenceGroupMap) 
         let f eqc = case typeOfGroup syns eqc of 
                        Nothing -> internalError "Top.TypeGraph.TypeGraphSolver" "makeSubstitution" "inconsistent state"
                        Just tp -> return [ (v, tp) | (v,_) <- vertices eqc, notId v tp ]
             notId i (TVar j) = i /= j
             notId _ _        = True
         res <- mapM f eqgroups
         return (concat res)
         
   -- add a new edge and propagate equality
   nextConstraintNumber =
      do i <- tgGets constraintNumber
         tgModify (\x -> x { constraintNumber = constraintNumber x + 1})
         return (makeEdgeNr i)
         
   -- add an edge and propagate equality (but don't introduce a new constraint number)
   addEdge edge@(EdgeID v1 v2) (cnr, info) =
      debugTrace ("addEdge " ++ show edge) >>      
      do combineClasses [v1, v2]
         updateEquivalenceGroupOf v1 (insertEdge edge cnr info)
         propagateEquality v1
              
   verticesInGroupOf i =
      do eqc <- equivalenceGroupOf i
         return (vertices eqc)

   edgesFrom i =
      do eqc <- equivalenceGroupOf i
         let p (EdgeID v1 v2,_,_) = v1 == i || v2 == i
         return (filter p (edges eqc))

   deleteEdge edge@(EdgeID v1 _) =
      debugTrace ("deleteEdge "++show edge) >>
      do updateEquivalenceGroupOf v1 (removeEdge edge)
         propagateRemoval v1

	 
   removeInconsistencies = 
      debugTrace "removeInconsistencies" >> 
      do hs         <- tgGets typegraphHeuristics
         (es, errs) <- applyHeuristics hs
         mapM_ deleteEdge es
         mapM_ addError errs 
         if null errs && null es
	   then -- everything is okay: no errors were found.
	        unmarkPossibleErrors
           else -- Bug patch 3 february 2004
	        -- safety first: check whether *everything* is really removed. 
	        removeInconsistencies
	 
   allPathsListWithout without v1 vs =
      debugTrace ("allPathsList' "++show v1++" "++show vs) >>
      do eqc <- equivalenceGroupOf v1
         return (equalPaths without v1 vs eqc)

   typeFromTermGraph i = 
      do vs <- verticesInGroupOf i
         case [ tp | (i', (tp, _)) <- vs, i == i' ] of
            [VCon s]   -> return (TCon s)
            [VApp a b] -> 
               do ta <- typeFromTermGraph a
                  tb <- typeFromTermGraph b
                  return (TApp ta tb)
            _ -> return (TVar i) 
   
   markAsPossibleError i =
      addPossibleInconsistentGroup i
      
   getMarkedPossibleErrors = 
      getPossibleInconsistentGroups
      
   unmarkPossibleErrors =
      setPossibleInconsistentGroups []

makeNewVertex :: HasTypeGraph m info => VertexInfo -> m Int
makeNewVertex vertexInfo =
   do i <- nextUnique                
      addVertex i vertexInfo
      return i
      
addClique :: Clique -> TypeGraphX info qs ext ()
addClique clique =
   debugTrace ("addClique " ++ show clique) >>
   do combineClasses (childrenInClique clique)
      eqc <- equivalenceGroupOf (cliqueRepresentative clique)
      updateEquivalenceGroupOf (cliqueRepresentative clique) (insertClique clique)

splitClass ::  Int -> TypeGraphX info qs ext [Int]
splitClass i = 
   do eqgroup <- equivalenceGroupOf i
      let newGroups = splitGroup eqgroup
      if (length newGroups > 1)
        then
           do removeGroup eqgroup
              mapM createNewGroup newGroups
        else
           return [i]

combineClasses :: [Int] -> TypeGraphX info qs ext ()
combineClasses is = 
   do xs <- mapM representativeInGroupOf is
      case nub xs of 
         list@(_:_:_) ->
            debugTrace ("combineClasses " ++ show list) >>
            do eqgroups <- mapM equivalenceGroupOf list
               mapM removeGroup eqgroups
               i <- createNewGroup (foldr combineGroups emptyGroup eqgroups)
               addPossibleInconsistentGroup i
         _ -> 
            return () 
               
deleteClique :: Clique -> TypeGraphX info qs ext ()
deleteClique clique = 
   debugTrace ("deleteClique " ++ show clique) >>
   updateEquivalenceGroupOf 
      (cliqueRepresentative clique)
      (removeClique clique)
         
propagateEquality :: Int -> TypeGraphX info qs ext () -- HasTypeGraph m info => Int -> m ()
propagateEquality i =
   debugTrace ("propagateEquality " ++ show i)  >>
   do (listLeft, listRight) <- childrenInGroupOf i
   
      left  <- mapM (representativeInGroupOf . child) listLeft
      right <- mapM (representativeInGroupOf . child) listRight
        
      when (length listLeft > 1) $
         do addClique (makeClique listLeft)
            addClique (makeClique listRight)
      
      when (length (nub left) > 1) $
         propagateEquality (head left)
         
      when (length (nub right) > 1) $ 
         propagateEquality (head right)

propagateRemoval :: Int -> TypeGraphX info qs ext ()
propagateRemoval i = 
   debugTrace ("propagateRemoval " ++ show i)  >> 
   do is <- splitClass i   
      ts <- mapM childrenInGroupOf is
      
      let (leftList, rightList) = unzip ts
          cliqueLeft  = makeClique (concat leftList)
          cliqueRight = makeClique (concat rightList)
          newCliques  = [ makeClique list | list <- leftList ++ rightList, length list > 1 ] 
          children    = [ child pc | pc:_ <- leftList ++ rightList ]
      
      when (length (filter (not . null) leftList) > 1) $
         do deleteClique cliqueLeft
            deleteClique cliqueRight
            mapM_ addClique newCliques
            mapM_ propagateRemoval children



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