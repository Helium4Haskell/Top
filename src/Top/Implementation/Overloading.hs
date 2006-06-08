{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  bastiaan@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Top.Implementation.Overloading  where

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
import Data.List (intersperse, (\\), partition, find)

import Debug.Trace
import Top.Implementation.PredGraph.Graph (constructGraph, constructGraphT, RuleEnv, Rule)
import Data.Graph.Inductive.Graph(nodes,edges, out, outdeg, lab, Graph)
import Data.Graph.Inductive.NodeMap(mkNode_, NodeMap)
import Data.Graph.Inductive.Graphviz(graphviz')

------------------------------------------------------------------------
-- (I)  Algebraic data type

data OverloadingState info = OverloadingState 
   { classEnvironment      :: ClassEnvironment            -- ^ All known type classes and instances
   , predicateMap          :: PredicateMap info           -- ^ Type class assertions
   , typeClassDirectives   :: TypeClassDirectives info    -- ^ Directives for type class assertions
   , dictionaryEnvironment :: DictionaryEnvironment2       -- ^ Dictionaries for constructing evidence
   }
   
------------------------------------------------------------------------
-- (II)  Instance of SolveState (Empty, Show)

instance Empty (OverloadingState info) where
   empty = OverloadingState 
      { classEnvironment      = emptyClassEnvironment
      , predicateMap          = empty
      , typeClassDirectives   = []
      , dictionaryEnvironment = emptyDictionaryEnvironment
      }

instance Show (OverloadingState info) where
   show s = unlines [ "class environment: " ++ concat (intersperse "," (M.keys (classEnvironment s)))
                    , "directives: " ++ show (typeClassDirectives s)
                    , "predicates: " ++ show (predicateMap s)
                    , "dict. environment: " ++ show (dictionaryEnvironment s)
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

   getDictionaryEnvironment =
      gets dictionaryEnvironment
      
   proveQualifier info p =
      modifyPredicateMap (\qm -> qm { globalQualifiers = (p, info) : globalQualifiers qm })

   assumeQualifier info p =
      do modifyPredicateMap (\qm -> qm { globalAssumptions = (p, info) : globalAssumptions qm })
         addDeclDictionaries info [p]

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
         
   generalizeWithQualifiers monos tp info =
      do preds1 <- proveQsSubst
         preds2 <- generalizedQsSubst
         let is       = ftv tp \\ ftv monos
             p        = any (`elem` is) . ftv . fst
             (as, bs) = partition p preds1
             cs       = filter    p preds2
             ps       = map fst (as ++ cs)
         modifyPredicateMap (\qm -> qm { globalQualifiers = bs, globalGeneralizedQs = as ++ globalGeneralizedQs qm })
         addDeclDictionaries info ps
         return (generalize monos (ps .=>. tp))

   -- improveQualifiersFinal -- use Default directives

   simplifyQualifiers monos =
      do preds       <- proveQsSubst
         assumptions <- assumeQsSubst
         syns        <- select getTypeSynonyms
         classEnv    <- getClassEnvironment
         directives  <- gets typeClassDirectives
         let (fr, nfr) = partition (freePredicate monos) preds
         (prds, varMap) <- select (resolve syns classEnv directives fr assumptions)
         modifyPredicateMap (\qm -> qm { globalQualifiers = prds ++ nfr }) 
         modifyVarMap (\vm -> M.unionWith (++) vm varMap)

   ambiguousQualifiers =
      do ps <- proveQsSubst
         select (ambiguous ps)

------------------------------------------------------------------------
-- Resolving predicates with by constructing a graph, and choose a
-- solution from the Graph.
------------------------------------------------------------------------

data Pred   = Pred Predicate
            | And [Predicate]
            | Assume Predicate (Int, Int)
            | Prove Predicate (Int, Int)
            deriving (Eq, Ord, Show)

truePred :: Pred
truePred = And []

unPred :: Pred -> Predicate
unPred (Pred p) = p
unPred _        = error "Only a (Pred p) can be unPred'ed"

isAssumePred :: Pred -> Bool
isAssumePred (Assume _ _) = True
isAssumePred _            = False

provePred :: (TypeConstraintInfo info) => (Predicate, info) -> Pred 
provePred (pred, info) = Prove pred (fromJust (overloadedIdentifier info))

assumePred :: (TypeConstraintInfo info) => (Predicate, info) -> Pred
assumePred (pred, info) = Assume pred (fromJust (overloadedIdentifier info))

resolve :: (HasTI m info, TypeConstraintInfo info, HasBasic m info)
               => OrderedTypeSynonyms -> ClassEnvironment -> TypeClassDirectives info
               -> [(Predicate, info)] -> [(Predicate, info)] -> m ([(Predicate, info)], M.Map (Int, Int) [DictionaryTree])
resolve syns classEnv directives prv ass = return (remaining gr, M.fromListWith (++) dTrees)
  where prvPrds  = map provePred  prv 
        assPrds  = map assumePred ass
        ruleEnv  = class2rule syns classEnv
        (gr, nm) = constructGraphT ruleEnv (prvPrds ++ assPrds)
        dTrees   = map (constructDictTree (gr, nm)) prvPrds

remaining :: Graph gr => gr Pred b -> [(Predicate, info)]
remaining tree
  = map (flip (,) (error "this info should not be used") . unPred) . filter (\p -> p /= truePred && not (isAssumePred p)) $ preds
  where nds = filter (\n -> (outdeg tree n) == 0) (nodes tree)
        preds = map (fromJust . lab tree) nds

constructDictTree :: Graph gr => (gr Pred String, NodeMap Pred) -> Pred -> ((Int, Int), [DictionaryTree])
constructDictTree (gr, nm) (Prove pred i) = (i, [edge nd (unPred p)])
  where (nd, p) = mkNode_ nm (Pred pred)
        edge nd pred = let edges = out gr nd 
                       in case selectEdge edges of 
                               Just (fnd, tnd, "inst") -> byInst  pred tnd
                               Just (fnd, tnd, "sup")  -> bySuper pred tnd
                               Just (fnd, tnd, "ass")  -> ByPredicate pred 
                               Nothing                 -> ByPredicate pred 

        bySuper (Predicate sub _) to = let  p@(Predicate sup _) = unPred . fromJust $ lab gr to
                                       in BySuperClass sup sub (edge to p)

        byInst p@(Predicate nm tp) to = let (TCon instName, _) = leftSpine tp
                                        in case fromJust (lab gr to) of
                                               And []    -> ByPredicate p
                                               And preds -> ByInstance nm instName (map (\(_, nd, _) -> edge nd (unPred . fromJust $ lab gr nd) ) (out gr to))
                                               Pred pred -> ByInstance nm instName [(edge to pred)]

        selectEdge edges = listToMaybe . catMaybes $
                           [ find (\(_, _, s) -> s == "ass") edges
                           , find (\(_, _, s) -> s == "inst") edges 
                           , find (\(_, _, s) -> s == "sup") edges 
                           ]

constructDictTree _ _ = error "Dictionary trees can only be constructed for Proof predicates."
   

class2rule :: OrderedTypeSynonyms -> ClassEnvironment -> RuleEnv Pred String
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



addDeclDictionaries :: (MonadState (OverloadingState info) m, TypeConstraintInfo info) => info -> [Predicate] -> m ()
addDeclDictionaries info ps = 
  do let id = overloadedIdentifier info
     if isJust id
      then modifyDictionaryEnvironment (\s -> s { declMap = M.insertWith (++) (fromJust id) ps (declMap s) } )
      else return ()

modifyVarMap :: MonadState (OverloadingState info) m => (M.Map (Int, Int) [DictionaryTree] -> M.Map (Int, Int) [DictionaryTree]) -> m ()
modifyVarMap f = modifyDictionaryEnvironment (\s -> s { varMap = f (varMap s) })

modifyPredicateMap :: MonadState (OverloadingState info) m => (PredicateMap info -> PredicateMap info) -> m ()
modifyPredicateMap f = 
   modify (\s -> s { predicateMap = f (predicateMap s) })

modifyDictionaryEnvironment :: MonadState (OverloadingState info) m => (DictionaryEnvironment2 -> DictionaryEnvironment2) -> m ()
modifyDictionaryEnvironment f = 
   modify (\s -> s { dictionaryEnvironment = f (dictionaryEnvironment s) })

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

freePredicate :: Tps -> (Predicate, info) -> Bool
freePredicate monos (Predicate _ tp, _) = not (elem tp monos)


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
