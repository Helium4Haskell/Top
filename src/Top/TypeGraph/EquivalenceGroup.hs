-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An equivalence group is a graph-like structure containing type variables and 
-- type constants that should all be equivalent. The edges explain why they should
-- be equal.
--
-----------------------------------------------------------------------------

module Top.TypeGraph.EquivalenceGroup 
   ( EquivalenceGroup 
   , emptyGroup, insertVertex, insertEdge, combineGroups
   , vertices, constants, edges, equalPaths
   , removeEdge, removeClique, splitGroup
   , typeOfGroup, combineCliques, consistent
   ) where

import Top.TypeGraph.Paths
import Top.TypeGraph.Basics
import Top.Types
import Utils (internalError)
import Debug.Trace (trace)
import Data.List
import qualified Data.Set as S

-----------------------------------------------------------------------
-- * Representation of an equivalence group

data EquivalenceGroup info = 
   EQGroup { vertices :: [(VertexID,VertexInfo)]        -- ^ vertices in this equivalence group
           , edges    :: [(EdgeID,Int,info)]            -- ^ (initial) edges in this equivalence group
           , cliques  :: [(Int,[(VertexID,VertexID)])]  -- ^ (implied) cliques in this equivalence group
           }

-- first sort the items of an equivalence group
instance Show (EquivalenceGroup info) where
   show eqgroup = 
      unlines [ "[Vertices ]: "++show (sort (vertices eqgroup))
              , "[Edges    ]: "++show (sort [ a | (a, _, _) <- edges eqgroup ])
              , "[Cliques  ]: "++show (sort [ (i, sort xs) | (i,xs) <- cliques eqgroup ])
              ]

-----------------------------------------------------------------------
-- * Constructing an equivalence group

emptyGroup :: EquivalenceGroup info
emptyGroup = 
   EQGroup { vertices = [] 
           , edges    = [] 
           , cliques  = []
           }
	   
insertVertex :: VertexID -> VertexInfo -> EquivalenceGroup info -> EquivalenceGroup info
insertVertex i info eqgroup = 
   eqgroup { vertices = (i, info) : vertices eqgroup }  

insertEdge :: EdgeID -> Int -> info -> EquivalenceGroup info -> EquivalenceGroup info
insertEdge i cnr info eqgroup = 
   eqgroup { edges = (i,cnr,info) : edges eqgroup }  
 
{- updated 3 december 2002: improvement in combining cliques -}
combineCliques :: Cliques -> EquivalenceGroup info -> EquivalenceGroup info 
combineCliques (i,lists) eqgroup = 
   (if debugTypeGraph then trace msg else id) 
   eqgroup { cliques = newCliques }

      where newCliques = filter ((>1) . length . snd) (new : cs1)
            p (j,list) = i /= j || all (`notElem` concat lists) list
            (cs1,cs2)  = partition p (cliques eqgroup)
            new        = (i,(nub . concat) (lists++map snd cs2))
	    
            msg = unlines [ "------------------combine clique -------------------------"
                          , show eqgroup
                          , "---- new cliques ----"
                          , show newCliques
                          ]

combineGroups :: EquivalenceGroup info -> EquivalenceGroup info -> EquivalenceGroup info
combineGroups eqgroup1 eqgroup2 = 
   EQGroup { vertices = vertices eqgroup1 ++ vertices eqgroup2
           , edges    = edges    eqgroup1 ++ edges    eqgroup2
           , cliques  = cliques  eqgroup1 ++ cliques  eqgroup2
           }
	   
----------------------------------------------------------------------
-- * Removing parts from an equivalence group

removeEdge :: EdgeID -> EquivalenceGroup info -> EquivalenceGroup info
removeEdge edge eqgroup =
   let p (e, _, _) = edge /= e
   in eqgroup { edges = filter p (edges eqgroup) }

{- Bug fix March 5, 2004: there should be an 'all' in the predicate 'p' -}
removeClique :: Cliques -> EquivalenceGroup info -> EquivalenceGroup info
removeClique (i,lists) eqgroup =
   (if debugTypeGraph then trace msg else id) 
   eqgroup { cliques = newCliques }

      where newCliques = zip (repeat i) (filter ((>1) . length) lists) ++ filter p (cliques eqgroup)
            p (j,list) = (i /= j || all (`notElem` concat lists) list) && length list > 1  
            
            msg = unlines [ "------------------remove clique -------------------------"
                          , show eqgroup
                          , "---- new cliques ----"
                          , show newCliques
                          ] 
			  
splitGroup :: EquivalenceGroup info -> [EquivalenceGroup info]
splitGroup eqc = 
   let (vs,es,cs) = (vertices eqc,edges eqc,cliques eqc)
       eqcs = map (\(a,b) -> insertVertex a b emptyGroup) vs

       addClique (cnr,list) cs 
          | length list < 2 = cs
          | null cs1        = internalError "Top.TypeGraph.EquivalenceGroup" "splitGroup" ("unexpected empty list (1)")
          | otherwise       = combineCliques (cnr,[list]) (foldr combineGroups emptyGroup cs1) : cs2
        
         where (cs1,cs2) = partition p cs 
               p c       = any ((`elem` is) . fst) (vertices c)
               is        = map fst list

       addEdge (EdgeID v1 v2,cnr,info) cs 
          | null cs1  = internalError "Top.TypeGraph.EquivalenceGroup" "splitGroup" "unexpected empty list (2)"
          | otherwise = insertEdge (EdgeID v1 v2) cnr info (foldr combineGroups emptyGroup cs1) : cs2
          
         where (cs1,cs2) = partition p cs
               p c       = any ((`elem` [v1,v2]) . fst) (vertices c)

   in foldr addEdge (foldr addClique eqcs cs) es			  

----------------------------------------------------------------------
-- * Interrogating an equivalence group

constants :: EquivalenceGroup info -> [String]
constants eqgroup = 
   nub [ s | (_, (VCon s, _)) <- vertices eqgroup ]
   
consistent :: EquivalenceGroup info -> Bool
consistent eqgroup = 
   case constants eqgroup of
      []  -> True
      [_] -> null [ () | (_, (VApp _ _, _)) <- vertices eqgroup ]
      _   -> False
      
equalPaths  :: S.Set VertexID -> VertexID -> [VertexID] -> EquivalenceGroup info -> Path (EdgeID, EdgeInfo info)
equalPaths without v1 targets eqgroup =
   (if debugTypeGraph then trace msg else id)  
   tailSharingBy compare $
      rec v1 (edgeList, cliqueList)  

    where   
      msg        = "Path from "++show v1++" to "++show targets++" without "++show (S.setToList without)
      edgeList   = [ edge   | edge@(EdgeID v1 v2,_,_) <- edges eqgroup, not (v1 `S.elementOf` without), not (v2 `S.elementOf` without) ]
      cliqueList = [ (childNr, filter (\(i, _) -> not (i `S.elementOf` without)) members) | (childNr, members) <- cliques eqgroup ]
      targetSet  = S.mkSet targets
      
      -- Allow a second visit of a clique in a path?
      secondCliqueVisit = False
      
      rec :: Int -> ([(EdgeID, Int, info)],[Clique]) -> Path (EdgeID, EdgeInfo info)
      rec v1 (es, cliques)
        | v1 `S.elementOf` targetSet  = Empty
        | otherwise =
             let (edges1,es' ) = partition (\(EdgeID a _,_,_) -> v1 == a) es
                 (edges2,es'') = partition (\(EdgeID _ a,_,_) -> v1 == a) es'
                 (neighbourCliques, otherCliques) = partition (\(_, cl) -> any ((==v1) . fst) cl) cliques 
                 rest@(_, restCliques)
                    | secondCliqueVisit = (es'', removeFromClique v1 neighbourCliques ++ otherCliques)
                    | otherwise         = (es'', otherCliques)
             in 
                altList $ 
                map (\(EdgeID _ neighbour,cnr,info) -> 
                      Step (EdgeID v1 neighbour,Initial cnr info) 
                      :+: rec neighbour rest) edges1
             ++ map (\(EdgeID neighbour _,cnr,info) -> 
                      Step (EdgeID v1 neighbour,Initial cnr info) 
                      :+: rec neighbour rest) edges2
             ++ concatMap (\(cnr, cliqueList) ->
                           let (sources, others) = partition ((v1==) . fst) cliqueList
                               sourceParents     = map snd sources
                               neighbours        = nub (map fst others)
                               f neighbour       = altList 
                                  [ steps :+: restPath
                                  | pair@(n, neighbourParent) <- others
                                  , n == neighbour
                                  , let restPath   
                                           | secondCliqueVisit = rec neighbour (es'', map f restCliques)
                                           | otherwise         = rec neighbour rest
                                        f (cnr,cl) = (cnr, filter (/= pair) cl)
                                        steps      = altList1 (map g sourceParents)
                                        g sp       = Step (EdgeID v1 neighbour, Implied cnr sp neighbourParent)
                                  ]
                           in if null sources 
                                then []
                                else map f neighbours) neighbourCliques
				
      removeFromClique :: VertexID -> [Clique] -> [Clique]
      removeFromClique vid cs = 
         [ (cnr, list')
         | (cnr, list) <- cs
         , let list' = filter ((/=vid) . fst) list
         , length list' > 1
         ]

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
                             Left _       -> Nothing
                             Right (_, s) -> Just $ equalUnderTypeSynonyms synonyms (s |-> t1) (s |-> t2)
                       op _ _ = Nothing                             
                   in foldr1 op (map Just xs)
   in        
      case (constantsList, childrenList) of 
         ([], [])          -> elseReturn (TVar representative)
         ([s], [])         -> elseReturn (TCon s)
         ([], (_,(l,r)):_) -> elseReturn (TApp (TVar l) (TVar r))
         _ -> Nothing
