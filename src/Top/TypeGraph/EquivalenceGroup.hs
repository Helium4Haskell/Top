-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.TypeGraph.EquivalenceGroup where

import Top.TypeGraph.Paths
import Top.TypeGraph.Basics
import Top.Types
import Data.List
import Utils (internalError)
import Debug.Trace (trace)

emptyGroup        ::                                                    EquivalenceGroup info
insertVertex      :: VertexID -> VertexInfo -> EquivalenceGroup info -> EquivalenceGroup info 
insertEdge        :: EdgeID -> Int -> info ->  EquivalenceGroup info -> EquivalenceGroup info 
combineCliques    :: Cliques ->                EquivalenceGroup info -> EquivalenceGroup info 
combineGroups     :: EquivalenceGroup info ->  EquivalenceGroup info -> EquivalenceGroup info
splitGroup        :: EquivalenceGroup info ->                         [ EquivalenceGroup info ]

removeEdge        :: EdgeID  -> EquivalenceGroup info -> EquivalenceGroup info
removeClique      :: Cliques -> EquivalenceGroup info -> EquivalenceGroup info

vertices          :: EquivalenceGroup info -> [(VertexID,VertexInfo)]
edges             :: EquivalenceGroup info -> [(EdgeID,Int,info)]
cliques           :: EquivalenceGroup info -> [Clique]
constants         :: EquivalenceGroup info -> [String]
consistent        :: EquivalenceGroup info -> Bool

pathsFrom         :: VertexID -> [VertexID] -> EquivalenceGroup info -> Path (EdgeID, EdgeInfo info)
pathsFromWithout  :: [VertexID] ->  VertexID -> [VertexID] -> EquivalenceGroup info -> Path (EdgeID, EdgeInfo info)

-----------------------------------------------------------------------------------------


----------------------------------------------------------------------
-- Representation of an equivalence group

newtype EquivalenceGroup info = 
   EQGroup ( [(VertexID,VertexInfo)]        -- variables
           , [String]                       -- constants
           , [(EdgeID,Int,info)]            -- (initial) edges
           , [(Int,[(VertexID,VertexID)])]  -- (implied) cliques
           )

-- first sort the items of an equivalence group for the Eq instance
instance Show (EquivalenceGroup info) where
   show (EQGroup (vs1,ss1,es1,cs1)) = 
      unlines [ "[Vertices ]: "++show (sort vs1)
              , "[Constants]: "++show (sort ss1)
              , "[Edges    ]: "++show (sort (map (\(a,_,_) -> a) es1))
              , "[Cliques  ]: "++show (sort (map f cs1))
              ]
         where f (i,xs) = (i,sort xs) 
         
instance Eq (EquivalenceGroup info) where
   a == x = show a == show x         
     

----------------------------------------------------------------------
-- Functions to construct an equivalence group

emptyGroup = EQGroup ([],[],[],[])

insertVertex i info (EQGroup (vs,ss,es,cs)) = (EQGroup ((i,info):vs,ss',es,cs))
   where ss' = case info of 
                  (VCon s,_) -> [s] `union` ss
                  _          -> ss
   
insertEdge i cnr info (EQGroup (vs,ss,es,cs)) = (EQGroup (vs,ss,(i,cnr,info):es,cs))  
 
 {- updated 3 december 2002: improvement in combining cliques -}
combineCliques (i,lists) (EQGroup (vs,ss,es,cs)) = 
   (if debugTypeGraph then trace msg else id) 
   (EQGroup (vs,ss,es,new))

      where new = filter ((>1) . length . snd) (newclass : cs1)
            (cs1,cs2) = let p (j,list) = i /= j || all (`notElem` concat lists) list
                        in partition p cs
            newclass  = (i,(nub . concat) (lists++map snd cs2))
            
            msg = unlines ["------------------combine clique -------------------------"
                          ,"status: "++ show (null [ x | (i,list) <- cs, (x,_) <- list, x `notElem` map fst vs ])
                          ,"vertices: "++show (map fst vs)                                    
                          ,"first: "++show cs
                          ,"clique: "++show (i,lists) 
                          ,"result: "++show new
                          ]

combineGroups (EQGroup (vs1,ss1,es1,cs1)) (EQGroup (vs2,ss2,es2,cs2)) = 
   EQGroup (vs1++vs2,ss1 `union` ss2,es1++es2,cs1++cs2)

splitGroup eqc = let (vs,es,cs) = (vertices eqc,edges eqc,cliques eqc)
                     eqcs = map (\(a,b) -> insertVertex a b emptyGroup) vs

                     addClique (cnr,list) cs 
                        | length list < 2 = cs
                        | null cs1        = internalError "Top.TypeGraph.EquivalenceGroup" "splitGroup" ("empty list (1) \n"++show eqc)
                        | otherwise       = combineCliques (cnr,[list]) (foldr combineGroups emptyGroup cs1) : cs2
                      
                       where (cs1,cs2) = partition p cs 
                             p c       = any ((`elem` is) . fst) (vertices c)
                             is        = map fst list
 
                     addEdge (EdgeID v1 v2,cnr,info) cs 
                        | null cs1  = internalError "Top.TypeGraph.EquivalenceGroup" "splitGroup" "empty list (2)"
                        | otherwise = insertEdge (EdgeID v1 v2) cnr info (foldr combineGroups emptyGroup cs1) : cs2
                        
                       where (cs1,cs2) = partition p cs
                             p c       = any ((`elem` [v1,v2]) . fst) (vertices c)

                 in foldr addEdge (foldr addClique eqcs cs) es

----------------------------------------------------------------------
-- Functions to remove parts of an equivalence group

removeEdge edge (EQGroup (vs1,ss1,es1,cs1)) = EQGroup (vs1,ss1,filter p es1,cs1)
   where p (e,_,_) = edge /= e

removeClique (i,lists) (EQGroup (vs,ss,es,cs)) = 
   (if debugTypeGraph then trace msg else id) 
   (EQGroup (vs,ss,es,new))
   
      where new = zip (repeat i) (filter ((>1) . length) lists) ++ filter p cs
            p (j,list) = (i /= j || any (`notElem` concat lists) list) && length list > 1  
            
            msg = unlines ["------------------remove clique -------------------------"
                          ,"status: "++ show (null [ x | (i,list) <- cs, (x,_) <- list, x `notElem` map fst vs ])
                          ,"vertices: "++show (map fst vs)                  
                          ,"first: "++show cs
                          ,"clique: "++show (i,lists) 
                          ,"result: "++show new
                          ] 
                      
----------------------------------------------------------------------
-- Functions to get the contents of an equivalence group

vertices   (EQGroup (vs1,ss1,es1,cs1)) = vs1
edges      (EQGroup (vs1,ss1,es1,cs1)) = es1
cliques    (EQGroup (vs1,ss1,es1,cs1)) = cs1
constants  (EQGroup (vs1,ss1,es1,cs1)) = ss1

consistent eqgroup = 
   case length (constants eqgroup) of
      0 -> True
      1 -> null [ () | (_, (VApp _ _, _)) <- vertices eqgroup ]
      _ -> False
    
----------------------------------------------------------------------
-- All paths between two vertices in a group 

pathsFrom = pathsFromWithout []

pathsFromWithout without v1 targets eqgroup
 | otherwise = 
   let edgeList   = [ edge   | edge@(EdgeID v1 v2,_,_) <- edges eqgroup, v1 `notElem` without, v2 `notElem` without ]
       cliqueList = [ (childNr, filter ((`notElem` without) . fst) members) | (childNr, members) <- cliques eqgroup ]
   in tailSharingBy compare
    $ rec v1 (edgeList, cliqueList) 

    where   
      rec :: Int -> ([(EdgeID, Int, info)],[Clique]) -> Path (EdgeID, EdgeInfo info)
      rec v1 (es,cs)
        | v1 `elem` targets  = Empty
        | otherwise = let (edges1,es' ) = partition (\(EdgeID a _,_,_) -> v1 == a) es
                          (edges2,es'') = partition (\(EdgeID _ a,_,_) -> v1 == a) es'
                          (cliques,cs') = partition (elem v1 . map fst . snd) cs
                          rest = (es'',cs')
                      in altList $ 
                         map (\(EdgeID _ neighbour,cnr,info) -> 
                               Step (EdgeID v1 neighbour,Initial cnr info) 
                               :+: rec neighbour rest) edges1
                      ++ map (\(EdgeID neighbour _,cnr,info) -> 
                               Step (EdgeID v1 neighbour,Initial cnr info) 
                               :+: rec neighbour rest) edges2
                      ++ concatMap (\(cnr,list) -> 
                                      let (list1, list2) = partition ((==v1) . fst) list 
                                      in [ Step (EdgeID v1 neighbour, Implied cnr v1parent parent)
                                             :+: recPath
                                         | (neighbour,parent) <- list2
                                         , let recPath = rec neighbour rest
                                         , (_, v1parent) <- list1
                                         ]) cliques                                                                                                              

-- a non-recursive function to find the type of an equivalence group
typeOfGroup :: OrderedTypeSynonyms -> EquivalenceGroup info -> Maybe Tp
typeOfGroup synonyms eqgroup = 
   let vertexList     = vertices eqgroup
       constantsList  = constants eqgroup
       childrenList   = [(v, (l,r)) |  (v, (VApp l r, _)) <- vertexList ]
       elseReturn tp  = Just (maybe tp id originalType)
       representative = fst (head vertexList)
       originalType   =
          case [ foldl TApp (TCon s) (map TVar is) | (_, (_, Just (s, is))) <- vertexList ]  of
             [] -> Nothing
             xs -> let op (Just t1) (Just t2) = 
                          case mguWithTypeSynonyms synonyms t1 t2 of
                             Left _      -> Nothing
                             Right (b,s) -> Just $ equalUnderTypeSynonyms synonyms (s |-> t1) (s |-> t2)
                       op _ _ = Nothing                             
                   in foldr1 op (map Just xs)
   in        
           case (constantsList, childrenList) of 
              ([], [])          -> elseReturn (TVar representative)
              ([s], [])         -> elseReturn (TCon s)
              ([], (_,(l,r)):_) -> elseReturn (TApp (TVar l) (TVar r))
              _ -> Nothing
