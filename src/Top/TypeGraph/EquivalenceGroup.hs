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
   , emptyGroup, insertVertex, insertEdge, insertClique, combineGroups
   , vertices, constants, edges, equalPaths
   , removeEdge, removeClique, splitGroup
   , typeOfGroup, consistent, checkGroup
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
   EQGroup { vertices :: [(VertexID, VertexInfo)]  -- ^ vertices in this equivalence group
           , edges    :: [(EdgeID, EdgeNr, info)]  -- ^ (initial) edges in this equivalence group
           , cliques  :: [Clique]                  -- ^ (implied) cliques in this equivalence group
           }

-- first sort the items of an equivalence group
instance Show (EquivalenceGroup info) where
   show eqgroup = 
      unlines $ 
              [ "[Vertices]:"
              , "   " ++ concatMap show (sort (vertices eqgroup))
              , "[Edges]:"
              , "   " ++ concatMap show (sort [ a | (a, _, _) <- edges eqgroup ])
              , "[Cliques  ]:"
              ] ++ 
              (map (("   "++). show) (sort  (cliques eqgroup)))

-----------------------------------------------------------------------
-- * Constructing an equivalence group

emptyGroup :: EquivalenceGroup info
emptyGroup = 
   EQGroup { vertices = [], edges = [], cliques = [] }
	   
insertVertex :: VertexID -> VertexInfo -> EquivalenceGroup info -> EquivalenceGroup info
insertVertex i info eqgroup = 
   eqgroup { vertices = (i, info) : vertices eqgroup }  

insertEdge :: EdgeID -> EdgeNr -> info -> EquivalenceGroup info -> EquivalenceGroup info
insertEdge i cnr info eqgroup = 
   eqgroup { edges = (i, cnr, info) : edges eqgroup }  
   
insertClique :: Clique -> EquivalenceGroup info -> EquivalenceGroup info 
insertClique clique eqgroup =
   (if debugTypeGraph then trace msg else id) 
   eqgroup { cliques = newCliques }
      
 where
   newCliques = mergeCliques (clique : cs2) : cs1
   (cs1, cs2) = partition (isDisjointClique clique) (cliques eqgroup)
	    
   msg = unlines [ "------------------insert clique -------------------------"
                 , show eqgroup
                 , "---- new cliques ----"
                 , show newCliques
                 ]

combineGroups :: EquivalenceGroup info -> EquivalenceGroup info -> EquivalenceGroup info
combineGroups eqgroup1 eqgroup2 = 
   EQGroup { vertices = vertices eqgroup1 ++ vertices eqgroup2
           , edges    = edges    eqgroup1 ++ edges    eqgroup2
           , cliques  = cliques  eqgroup1 `combineCliqueList` cliques  eqgroup2
           }
	   
----------------------------------------------------------------------
-- * Removing parts from an equivalence group

removeEdge :: EdgeID -> EquivalenceGroup info -> EquivalenceGroup info
removeEdge edge eqgroup =
   let p (e, _, _) = edge /= e
   in eqgroup { edges = filter p (edges eqgroup) }

removeClique :: Clique -> EquivalenceGroup info -> EquivalenceGroup info
removeClique clique eqgroup =
   eqgroup { cliques = filter (not . (`isSubsetClique` clique)) (cliques eqgroup) }
             
splitGroup :: EquivalenceGroup info -> [EquivalenceGroup info]
splitGroup eqgroup = 
   let (vs, es, cs) = (vertices eqgroup, edges eqgroup, cliques eqgroup)
       eqcs = map (\(a, b) -> insertVertex a b emptyGroup) vs

       addClique clique cs = 
          let is         = childrenInClique clique
              (cs1, cs2) = partition (any ((`elem` is) . fst) . vertices) cs    
          in insertClique clique (foldr combineGroups emptyGroup cs1) : cs2

       addEdge (EdgeID v1 v2,cnr,info) cs =
          let is         = [v1, v2] 
              (cs1, cs2) = partition (any ((`elem` is) . fst) . vertices) cs
          in insertEdge (EdgeID v1 v2) cnr info (foldr combineGroups emptyGroup cs1) : cs2

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
      
equalPaths  :: S.Set VertexID -> VertexID -> [VertexID] -> EquivalenceGroup info -> TypeGraphPath info
equalPaths without v1 targets eqgroup =
   --(if debugTypeGraph then trace msg else id)  
   tailSharingBy compare $
      rec v1 (edgeList, cliqueList)  

    where   
      msg        = "Path from "++show v1++" to "++show targets++" without "++show (S.setToList without)
      edgeList   = let p (EdgeID v1 v2,_,_) = 
                          not (v1 `S.elementOf` without) && not (v2 `S.elementOf` without)
                   in filter p (edges eqgroup)
      cliqueList = let f = filter (not . (`S.elementOf` without) . child) . triplesInClique
                   in map f (cliques eqgroup)
      targetSet  = S.mkSet targets
      
      -- Allow a second visit of a clique in a path?
      secondCliqueVisit = False
      
      rec :: Int -> ([(EdgeID, EdgeNr, info)], [[ParentChild]]) -> TypeGraphPath info
      rec v1 (es, cliques)
        | v1 `S.elementOf` targetSet  = Empty
        | otherwise =
             let (edges1,es' ) = partition (\(EdgeID a _,_,_) -> v1 == a) es
                 (edges2,es'') = partition (\(EdgeID _ a,_,_) -> v1 == a) es'
                 (neighbourCliques, otherCliques) = 
                    partition ((v1 `elem`) . map child) cliques 
                 rest@(_, restCliques)
                    | secondCliqueVisit = (es'', removeFromClique v1 neighbourCliques ++ otherCliques)
                    | otherwise         = (es'', otherCliques)
             in 
                altList $ 
                map (\(EdgeID _ neighbour, cnr, info) -> 
                      Step (EdgeID v1 neighbour, Initial cnr info) 
                      :+: rec neighbour rest) edges1
             ++ map (\(EdgeID neighbour _, cnr, info) -> 
                      Step (EdgeID v1 neighbour, Initial cnr info) 
                      :+: rec neighbour rest) edges2
             ++ concatMap (\list ->
                           let (sources, others) = partition ((v1==) . child) list
                               sourceParents     = map parent sources
                               neighbours        = nub (map child others)
                               f neighbour       = altList 
                                  [ steps :+: restPath
                                  | pc <- others
                                  , child pc == neighbour
                                  , let restPath   
                                           | secondCliqueVisit = rec neighbour (es'', map (filter (/= pc)) restCliques)
                                           | otherwise         = rec neighbour rest
                                        steps = altList1 (map g sourceParents)
                                        g sp = Step ( EdgeID v1 neighbour
                                                    , Implied (childSide pc) sp (parent pc)
                                                    )
                                  ]
                           in if null sources 
                                then []
                                else map f neighbours) neighbourCliques
				
      removeFromClique :: VertexID -> [[ParentChild]] -> [[ParentChild]]
      removeFromClique vid =
         let p pcs = length pcs > 1
             f pcs = filter ((/=vid) . child) pcs
         in filter p . map f

typeOfGroup :: OrderedTypeSynonyms -> EquivalenceGroup info -> Maybe Tp
typeOfGroup synonyms eqgroup = 
   let vertexList     = vertices eqgroup
       constantsList  = constants eqgroup
       childrenList   = [(v, (l,r)) |  (v, (VApp l r, _)) <- vertexList ]
       elseReturn tp  = Just (maybe tp id originalType)
       representative = fst (head vertexList)
       originalType   =
          case [ tp | (_, (_, Just tp)) <- vertexList ]  of
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
         
-- Check for some invariants: identity if everything is okay, otherwise an internal error
checkGroup :: EquivalenceGroup info -> EquivalenceGroup info
checkGroup = test c2 . test c1 where 
   test p eqGroup = if p eqGroup then error "Check failed for equivalence group" else eqGroup 
   c1 eqGroup = hasDouble (concatMap triplesInClique $ cliques eqGroup) 
   c2 eqGroup = any ((<2) . length . triplesInClique) (cliques eqGroup)
   hasDouble [] = False
   hasDouble (x:xs) = x `elem` xs || hasDouble xs