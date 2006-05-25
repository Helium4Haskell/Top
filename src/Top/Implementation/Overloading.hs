{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  bastiaan@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Implementation.Overloading where

import Top.Types hiding (contextReduction)
import qualified Top.Types (contextReduction)
import Top.Constraint.Information
import Top.Implementation.General
import Top.Interface.TypeInference (getTypeSynonyms, HasTI, getSkolems)
import Top.Interface.Basic
import Top.Interface.Substitution
import Top.Interface.Qualification
import Top.Monad.Select
import Top.Util.Embedding
import qualified Data.Map as M
import Data.Maybe
import Data.List (intersperse, (\\), partition)

import Debug.Trace
import Top.Implementation.PredGraph.Graph (constructGraph, constructGraphT, RuleEnv, Rule)
import Data.Graph.Inductive.Graph(nodes,edges, outdeg, lab, Graph)
import Data.Graph.Inductive.Graphviz(graphviz')

------------------------------------------------------------------------
-- (I)  Algebraic data type

data OverloadingState info = OverloadingState 
   { classEnvironment    :: ClassEnvironment            -- ^ All known type classes and instances
   , predicateMap        :: PredicateMap info           -- ^ Type class assertions
   , typeClassDirectives :: TypeClassDirectives info    -- ^ Directives for type class assertions
   }
   
------------------------------------------------------------------------
-- (II)  Instance of SolveState (Empty, Show)

instance Empty (OverloadingState info) where
   empty = OverloadingState 
      { classEnvironment    = emptyClassEnvironment
      , predicateMap        = empty
      , typeClassDirectives = []
      }

instance Show (OverloadingState info) where
   show s = unlines [ "class environment: " ++ concat (intersperse "," (M.keys (classEnvironment s)))
                    , "directives: " ++ show (typeClassDirectives s)
                    , "predicates: " ++ show (predicateMap s)
                    ] 

instance Show info => SolveState (OverloadingState info) where 
   stateName _ = "OverloadingState State"
   
------------------------------------------------------------------------
-- (III)  Embeddings

instance Embedded ClassQual (OverloadingState info) (OverloadingState info)                where embedding = idE
instance Embedded ClassQual (Simple (OverloadingState info) x m) (OverloadingState info)   where embedding = fromFstSimpleE embedding 

------------------------------------------------------------------------
-- (IV)  Instance declaration

instance ( MonadState s m
         , HasBasic m info
         , HasTI    m info
         , TypeConstraintInfo info
         , Embedded ClassQual s (OverloadingState info)
         ) =>
           HasQual (Select (OverloadingState info) m) info where

   setClassEnvironment env =
      modify (\s -> s { classEnvironment = env })
      
   getClassEnvironment =
      gets classEnvironment
      
   proveQualifier info p =
      modifyPredicateMap (\qm -> qm { globalQualifiers = (p, info) : globalQualifiers qm })

   assumeQualifier info p =
      modifyPredicateMap (\qm -> qm { globalAssumptions = (p, info) : globalAssumptions qm })

   changeQualifiers f =
      do let g = mapM (\(p, info) -> f p >>= \new -> return (new, info) )
         as <- gets (globalQualifiers    . predicateMap) >>= g
         bs <- gets (globalGeneralizedQs . predicateMap) >>= g
         cs <- gets (globalAssumptions   . predicateMap) >>= g
         modifyPredicateMap (\qm -> qm { globalQualifiers    = as 
                                       , globalGeneralizedQs = bs
                                       , globalAssumptions   = cs })

   allQualifiers = 
      do syns     <- select getTypeSynonyms
         classEnv <- getClassEnvironment
         qmap     <- gets predicateMap
         let ps = globalQualifiers qmap ++ globalGeneralizedQs qmap ++ globalAssumptions qmap
         return (fst (Top.Types.contextReduction syns classEnv (map fst ps)))
         
   generalizeWithQualifiers monos tp =
      do preds1 <- proveQsSubst
         preds2 <- generalizedQsSubst
         let is       = ftv tp \\ ftv monos
             p        = any (`elem` is) . ftv . fst
             (as, bs) = partition p preds1
             cs       = filter    p preds2
         modifyPredicateMap (\qm -> qm { globalQualifiers = bs, globalGeneralizedQs = as ++ globalGeneralizedQs qm })
         return (generalize monos (map fst (as ++ cs) .=>. tp))


   -- improveQualifiersFinal -- use Default directives

   simplifyQualifiers =
      do preds       <- proveQsSubst
         assumptions <- assumeQsSubst
         syns        <- select getTypeSynonyms
         classEnv    <- getClassEnvironment
         directives  <- gets typeClassDirectives
         prds        <- select (resolve syns classEnv directives preds assumptions)
        -- let final = filter (not . entail syns classEnv (map fst assumptions) . fst) new
         modifyPredicateMap (\qm -> qm { globalQualifiers = prds })

   ambiguousQualifiers =
      do ps <- proveQsSubst
         select (ambiguous ps)

------------------------------------------------------------------------
-- Resolving predicates with by constructing a graph, and choose a
-- solution from the Graph.
------------------------------------------------------------------------

data Pred info = Pred Predicate
               | And [Predicate]
               | Assume Predicate info  
               | Prove Predicate info
               deriving (Eq, Ord, Show)

truePredicate = And []

unPred (Pred p) = p
unPred _        = error "Only a (Pred p) can be unPred'ed"

isAssumePredicate (Assume _ _) = True
isAssumePredicate _            = False

-- resolve :: (HasTI m info, TypeConstraintInfo info, HasBasic m info)
--                => OrderedTypeSynonyms -> ClassEnvironment -> TypeClassDirectives info
--                -> [(Predicate, info)] -> [(Predicate, info)] -> m [(Predicate, info)]
resolve syns classEnv directives prvPrds assPrds = return  (trace (graphviz' gr ++ "\n\n") (remaining gr)) 
  where prds     = map (uncurry Prove)  prvPrds ++ map (uncurry Assume) assPrds
        ruleEnv  = class2rule syns classEnv
        (gr, nm) = constructGraphT ruleEnv prds

-- remaining :: Graph gr => gr Pred b -> [Pred]
remaining tree
  = map (flip (,) emptyInfo . unPred) . filter (\p -> p /= truePredicate && not (isAssumePredicate p)) $ preds
  where nds = filter (\n -> (outdeg tree n) == 0) (nodes tree)
        preds = map (fromJust . lab tree) nds
   

class2rule :: OrderedTypeSynonyms -> ClassEnvironment -> RuleEnv (Pred info) String
class2rule _ _ c@(Prove  p _) = [(c, Pred p, "prv")]
class2rule _ _ c@(Assume p _) = [(Pred p, c, "ass")]
class2rule syns classEnv c@(Pred p) = instRules ++ supRules
 where superClasses = map Pred (bySuperclass' classEnv p)
       supRules     = zip3 superClasses (repeat c) (repeat "sup")
       instRules    = case byInstance syns classEnv p of
                       Nothing -> []
                       (Just [nd]) -> [(c, Pred nd, "inst")]
                       (Just nds)  -> (c, andClasses, "inst") : zip3 (repeat andClasses) instClasses (repeat "and")
                                      where andClasses = And nds
                                            instClasses = map Pred nds
class2rule _ _ _ = []

ambiguous :: (HasBasic m info, HasTI m info, TypeConstraintInfo info)
                => [(Predicate, info)] -> m ()
ambiguous listStart =
   do skolems <- getSkolems
      let skolemPairs = [ (is, info) | (is, info, _) <- skolems ]

          reportAmbiguous (p, info) =
             addLabeledError ambiguousLabel (ambiguousPredicate p info)

          reportMissing pair info2 =
             addLabeledError missingInSignatureLabel (predicateArisingFrom pair info2)
          
          f pair@(Predicate _ (TVar i), _) = 
             case [ info2 | (is, info2) <- skolemPairs, i `elem` is ] of
                info2:_ -> reportMissing pair info2
                _       -> reportAmbiguous pair
          f pair = reportAmbiguous pair

      mapM_ f listStart

modifyPredicateMap :: MonadState (OverloadingState info) m => (PredicateMap info -> PredicateMap info) -> m ()
modifyPredicateMap f = 
   modify (\s -> s { predicateMap = f (predicateMap s) })

proveQsSubst, assumeQsSubst, generalizedQsSubst :: 
   (MonadState s m, Embedded ClassQual s (OverloadingState info) {-, MonadState s m, HasSubst m info -}) 
      => Select (OverloadingState info) m [(Predicate, info)]

proveQsSubst       = gets (globalQualifiers    . predicateMap) -- >>= select . mapM substPredicate
assumeQsSubst      = gets (globalAssumptions   . predicateMap) -- >>= select . mapM substPredicate
generalizedQsSubst = gets (globalGeneralizedQs . predicateMap) -- >>= select . mapM substPredicate

substPredicate :: HasSubst m info => (Predicate, info) -> m (Predicate, info)
substPredicate (p, info) = 
   do new <- applySubst p
      return (new, info)

-- Type class directives
type TypeClassDirectives info = [TypeClassDirective info]

data TypeClassDirective info 
   = NeverDirective     Predicate  info
   | CloseDirective     String     info
   | DisjointDirective  [String]   info
   | DefaultDirective   String Tps info

instance Show (TypeClassDirective info) where
   show _ = "<<type class directive>>"
   
-- Predicate map
data PredicateMap info = 
   PredicateMap
      { globalQualifiers    :: [(Predicate, info)]
      , globalGeneralizedQs :: [(Predicate, info)]
      , globalAssumptions   :: [(Predicate, info)]
      }
     
instance Show (PredicateMap info) where
   show qm = 
      let f (s, sf)
             | null ps   = []
             | otherwise = ["   " ++ s ++ ": " ++ concat (intersperse "," (map (show . fst) ps))]
            where ps = sf qm 
      in unlines $ concatMap f 
            [ ("qualifiers"            , globalQualifiers)
            , ("generalized qualifiers", globalGeneralizedQs)
            , ("assumptions"           , globalAssumptions)
            ]
 
instance Empty (PredicateMap info) where
   empty = PredicateMap { globalQualifiers = [], globalGeneralizedQs = [], globalAssumptions = [] }
   
instance Substitutable (PredicateMap info) where
   sub |-> (PredicateMap as bs cs) = 
      let as' = [ (sub |-> a, info) | (a, info) <- as ]
          bs' = [ (sub |-> b, info) | (b, info) <- bs ]
          cs' = [ (sub |-> c, info) | (c, info) <- cs ]
      in PredicateMap as' bs' cs'
   ftv (PredicateMap as bs cs) = ftv (map fst $ as ++ bs ++ cs)

unresolvedLabel :: ErrorLabel
unresolvedLabel = ErrorLabel "unresolved predicate"

disjointLabel :: ErrorLabel
disjointLabel = ErrorLabel "disjoint predicates"

ambiguousLabel :: ErrorLabel
ambiguousLabel = ErrorLabel "ambiguous predicate" 

missingInSignatureLabel :: ErrorLabel
missingInSignatureLabel = ErrorLabel "predicate missing in signature" 
