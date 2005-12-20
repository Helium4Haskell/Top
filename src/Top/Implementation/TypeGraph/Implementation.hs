module Top.TypeGraph.Implementation where

import Top.States.TIState (HasTI(..), getTypeSynonyms, nextUnique)
import Top.States.BasicState (HasBasic(..), addLabeledError)
import Top.States.SubstState
import Top.TypeGraph.TypeGraphMonad
import Top.TypeGraph.TypeGraphState (HasTypeGraph)
import Top.TypeGraph.EquivalenceGroup
import Top.TypeGraph.Basics
import Top.TypeGraph.ApplyHeuristics (applyHeuristics)
import Top.Types
import Utils (internalError)
import Control.Monad (when)
import Data.List (nub)
import Data.Set (Set)

------------------------------------------------------------
-- Abstract data type 

newtype TypeGraph info a = TypeGraph_ (forall m . (HasTypeGraph m info, HasBasic m info, HasTI m info, HasTG m info) => m a)

toTypeGraph :: (forall m . (HasTypeGraph m info, HasBasic m info, HasTI m info, HasTG m info) => m a) -> TypeGraph info a
toTypeGraph f = TypeGraph_ f

fromTypeGraph :: (HasTypeGraph m info, HasTG m info) => TypeGraph info a -> m a
fromTypeGraph (TypeGraph_ x) = x

instance Monad (TypeGraph info) where 
   return x  = toTypeGraph (return x) 
   tg1 >>= f = toTypeGraph (fromTypeGraph tg1 >>= fromTypeGraph . f)

instance HasTI (TypeGraph info) info where 
   tiGet   = toTypeGraph (tiGet) 
   tiPut x = toTypeGraph (tiPut x)
   
instance HasTG (TypeGraph info) info where 
  tgGet   = toTypeGraph (tgGet)
  tgPut x = toTypeGraph (tgPut x)
  
------------------------------------------------------------
-- Implementation based on equivalence groups

-- construct a type graph
addTermGraph :: Tp -> TypeGraph info VertexId
addTermGraph tp = 
   debugTrace ("addTermGraph " ++ show tp) >>
   do synonyms <- getTypeSynonyms
      let (newtp, original) = 
             case expandToplevelTC synonyms tp of
                Nothing -> (tp, Nothing) 
                Just x  -> (x, Just tp)
      case newtp of
         TVar i     -> return (VertexId i)
         TCon s     -> makeNewVertex (VCon s, original)
         TApp t1 t2 -> 
            do v1 <- addTermGraph t1
               v2 <- addTermGraph t2
               makeNewVertex (VApp v1 v2, original)
                                   
addVertex :: VertexId -> VertexInfo -> TypeGraph info ()
addVertex v info = 
   createGroup (insertVertex v info emptyGroup)

addEdge :: EdgeId -> info -> TypeGraph info ()
addEdge edge@(EdgeId v1 v2 _) info =
   debugTrace ("addEdge " ++ show edge) >>      
   do combineClasses [v1, v2]
      updateGroupOf v1 (insertEdge edge info)
      propagateEquality v1
         
-- deconstruct a type graph
deleteEdge :: EdgeId -> TypeGraph info ()
deleteEdge edge@(EdgeId v1 _ _) =
   debugTrace ("deleteEdge "++show edge) >>
   do updateGroupOf v1 (removeEdge edge)
      propagateRemoval v1

-- inspect an equivalence group in a type graph
verticesInGroupOf :: VertexId -> TypeGraph info [(VertexId, VertexInfo)]
verticesInGroupOf i =
   do eqc <- getGroupOf i
      return (vertices eqc)

childrenInGroupOf :: VertexId -> TypeGraph info ([ParentChild], [ParentChild])
childrenInGroupOf i =
   do vs <- verticesInGroupOf i 
      return $ unzip 
         [ ( ParentChild { parent=p, child = t1, childSide=LeftChild  }
           , ParentChild { parent=p, child = t2, childSide=RightChild } 
           ) 
         | (p, (VApp t1 t2, _)) <- vs 
         ] 
            
edgesFrom :: VertexId -> TypeGraph info [(EdgeId, info)]
edgesFrom i =
   do eqc <- getGroupOf i
      let p (EdgeId v1 v2 _, _) = v1 == i || v2 == i
      return (filter p (edges eqc))
         
-- query a path in an equivalence group         
allPathsListWithout :: Set VertexId -> VertexId -> [VertexId] -> TypeGraph info (TypeGraphPath info)
allPathsListWithout without v1 vs =
   debugTrace ("allPathsList' "++show v1++" "++show vs) >>
   do eqc <- getGroupOf v1
      return (equalPaths without v1 vs eqc)        
         
-- make the type graph consistent
removeInconsistencies :: TypeGraph info ()
removeInconsistencies = 
   debugTrace "removeInconsistencies" >> toTypeGraph rec 
 where
   rec :: (HasTypeGraph m info, HasTG m info) => m ()
   rec = do phs  <- getPathHeuristics
            errs <- applyHeuristics phs
            mapM_ (fromTypeGraph . deleteEdge) (concatMap fst errs)
            mapM_ (addLabeledError unificationErrorLabel . snd) errs 
            if null errs
	           then -- everything is okay: no errors were found.
	              fromTypeGraph unmarkPossibleErrors
               else -- Bug patch 3 february 2004
	                -- safety first: check whether *everything* is really removed. 
	              rec

substituteTypeSafe :: Tp -> TypeGraph info (Maybe Tp) 
substituteTypeSafe = rec []
  where
    rec history (TVar i)
      |  i `elem` history  =  return Nothing
      |  otherwise         =
            do  synonyms  <-  getTypeSynonyms
                eqgroup   <-  getGroupOf (VertexId i)
                case typeOfGroup synonyms eqgroup of
                   Just (TVar j)  ->  return (Just (TVar j))
                   Just newtp     ->  rec (i:history) newtp
                   Nothing        ->  return Nothing

    rec _ tp@(TCon _) = 
       return (Just tp)

    rec history (TApp l r) = 
       do  ml  <-  rec history l
           mr  <-  rec history r
           case (ml, mr) of
              (Just l', Just r')   ->  return (Just (TApp l' r'))
              _                    ->  return Nothing
              
makeSubstitution :: TypeGraph info [(VertexId, Tp)]
makeSubstitution =
   debugTrace ("makeSubstitution") >>
   do syns     <- getTypeSynonyms
      eqgroups <- getAllGroups
      let f eqgroup =
             case typeOfGroup syns eqgroup of 
                Just tp -> return [ (vid, tp) | (vid@(VertexId i), _) <- vertices eqgroup, notId i tp ]
                Nothing -> internalError "Top.TypeGraph.Implementation" "makeSubstitution" "inconsistent equivalence group"
          notId i (TVar j) = i /= j
          notId _ _        = True
      res <- mapM f eqgroups
      return (concat res)
         
typeFromTermGraph :: VertexId -> TypeGraph info Tp
typeFromTermGraph vid = 
   do vs <- verticesInGroupOf vid
      case [ tp | (x, (tp, _)) <- vs, vid == x ] of
         [VCon s]   -> return (TCon s)
         [VApp a b] -> 
            do ta <- typeFromTermGraph a
               tb <- typeFromTermGraph b
               return (TApp ta tb)
         _ -> return (vertexIdToTp vid)

-- Extra administration
markAsPossibleError :: VertexId -> TypeGraph info  ()
markAsPossibleError i = addPossibleInconsistentGroup i

getMarkedPossibleErrors :: TypeGraph info  [VertexId]
getMarkedPossibleErrors = getPossibleInconsistentGroups

unmarkPossibleErrors :: TypeGraph info ()
unmarkPossibleErrors = setPossibleInconsistentGroups []           
           
-- Helper functions
makeNewVertex :: VertexInfo -> TypeGraph info VertexId
makeNewVertex vertexInfo =
   do i <- nextUnique    
      addVertex (VertexId i) vertexInfo
      return (VertexId i)
      
combineClasses :: [VertexId] -> TypeGraph info ()
combineClasses is = 
   do xs <- mapM representativeInGroupOf is
      case nub xs of 
         list@(i:_:_) ->
            debugTrace ("combineClasses " ++ show list) >>
            do eqgroups <- mapM getGroupOf list
               mapM removeGroup eqgroups
               createGroup (foldr combineGroups emptyGroup eqgroups)
               addPossibleInconsistentGroup i
         _ -> 
            return ()
            
propagateEquality :: VertexId -> TypeGraph info ()
propagateEquality v =
   debugTrace ("propagateEquality " ++ show v)  >>
   do (listLeft, listRight) <- childrenInGroupOf v
      left  <- mapM (representativeInGroupOf . child) listLeft
      right <- mapM (representativeInGroupOf . child) listRight

      when (length listLeft > 1) $
         do addClique (makeClique listLeft)
            addClique (makeClique listRight)
      
      when (length (nub left) > 1) $ 
         propagateEquality (head left)
         
      when (length (nub right) > 1) $ 
         propagateEquality (head right)
 
addClique :: Clique -> TypeGraph info ()
addClique clique =
   debugTrace ("addClique " ++ show clique) >>
   do combineClasses (childrenInClique clique)
      updateGroupOf (cliqueRepresentative clique) (insertClique clique)
           
propagateRemoval :: VertexId -> TypeGraph info ()
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
            
splitClass ::  VertexId -> TypeGraph info [VertexId]
splitClass i = 
   do eqgroup <- getGroupOf i
      let newGroups = splitGroup eqgroup
      when (length newGroups > 1) $
         do removeGroup eqgroup
            mapM_ createGroup newGroups
      return [ vid | (vid, _):_ <- map vertices newGroups ]
           
deleteClique :: Clique -> TypeGraph info ()
deleteClique clique = 
   debugTrace ("deleteClique " ++ show clique) >>
   updateGroupOf 
      (cliqueRepresentative clique)
      (removeClique clique)

representativeInGroupOf :: VertexId -> TypeGraph info VertexId  
representativeInGroupOf i =
   do vs <- verticesInGroupOf i
      case vs of 
         (vid, _):_ -> return vid
         _ -> internalError "Top.TypeGraph.TypeGraphState" "representativeInGroupOf" "unexpected empty equivalence group"
