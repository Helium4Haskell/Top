module Top.Qualifiers.TypeClasses where

import Top.Types
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.Qualifiers.Qualifiers
import Top.Constraints.TypeConstraintInfo
import Top.Constraints.Constraints (solveConstraint)
import Top.Constraints.Equality ( (.==.) )
import Data.Maybe (isJust)
import Data.List
import Control.Monad (foldM)

instance ( TypeConstraintInfo info
         , HasBasic m info
         , HasTI m info
         , HasSubst m info
         ) => 
           Qualifier m info Predicate
   where
      entails ps p = 
         do syns     <- getTypeSynonyms
            classEnv <- getClassEnvironment
            return (entail syns classEnv (map fst ps) p)
   
      simplify psNew = 
         do syns      <- getTypeSynonyms
            classEnv  <- getClassEnvironment
            nevers    <- tiGets (neverDirectives    . typeclassDirectives)
            closes    <- tiGets (closeDirectives    . typeclassDirectives)
            disjoints <- tiGets (disjointDirectives . typeclassDirectives)
         
            let loopIn t@(p@(Predicate className _), info)
                   | inHeadNormalForm p = return [t]
                   | otherwise =                         
                        case byInstance syns classEnv p of
                           Just ps -> 
                              loopInList [ (q, parentPredicate p info) | q <- ps ]
                           Nothing ->
                              let neverList = filter (isJust . matchPredicates syns p . fst) nevers
                                  newInfo   = 
                                     case neverList of 
                                        tuple:_ -> neverDirective tuple info
                                        [] -> case lookup className closes of
                                                 Just i  -> closeDirective (className, i) info
                                                 Nothing -> unresolvedPredicate p info
                              in addLabeledError unresolvedLabel newInfo >> return []
                
                loopInList ts = 
                   do psList <- mapM loopIn ts
                      return (concat psList)
                
                loopSc rs [] = rs
                loopSc rs (x:xs) 
                   | scEntail classEnv (map fst (rs++xs)) (fst x)
                        = loopSc rs xs
                   | otherwise                    
                        = loopSc (x:rs) xs
                
                testDisjoints [] = return []
                testDisjoints (t@(Predicate className tp, info):ts) =
                   let f t'@(Predicate className' tp', info') = 
                          case [ i | tp == tp', (ss, i) <- disjoints, className `elem` ss, className' `elem` ss ] of
                             [] -> return ([t'], True)
                             infodir : _ ->
                                do addLabeledError disjointLabel (disjointDirective (className, info) (className', info') infodir)
                                   return ([], False)
                             
                   in do result <- mapM f ts
                         let (list, bs) = unzip result
                         rest <- testDisjoints (concat list)
                         return $ if and bs then t : rest else rest
                
            hnf <- loopInList psNew
            testDisjoints (loopSc [] hnf)
      
      ambiguous list =
         do list1 <- missingInSignature
         
            let (hnf, nothnf) = 
                   let op x@(Predicate _ (TVar i), _) (xs1, xs2) = ((i, x):xs1, xs2)
                       op x                           (xs1, xs2) = (xs1, x:xs2)
                   in foldr op ([], []) list1
                grouped = map (\((i, x):xs) -> (i, x : map snd xs))
                        $ groupBy (\x y -> fst x == fst y)
                        $ sortBy  (\x y -> fst x `compare` fst y) hnf
            list2 <- mapM tryToDefault grouped
            
            let f (p, info) = addLabeledError ambiguousLabel (ambiguousPredicate p info)
            mapM_ f (concat (nothnf : list2))
                  
       where
         -- a class predicate about a skolemized type variable cannot be proven
         missingInSignature =
            do sk    <- tiGets skolems
               skols <- let f (is, info, _) = 
                               do tps <- mapM findSubstForVar is
                                  return (ftv tps, info)
                        in mapM f sk
               let f xs x = 
                      case x of 
                         (p@(Predicate _ (TVar i)), info) -> 
                            case [ info2 | (is, info2) <- skols, i `elem` is ] of
                               info2:_ -> 
                                  let newinfo = predicateArisingFrom (p, info) info2
                                  in do addLabeledError missingInSignatureLabel newinfo
                                        return xs
                               _ -> return (x:xs)
                         _ -> return (x:xs)
               foldM f [] list
               
         -- try to use a defaulting directive before reporting an error message
         tryToDefault (i, ts) =
            do defaults   <- tiGets (defaultDirectives . typeclassDirectives)
               candidates <- 
                  let f (Predicate cn _) = 
                         case lookup cn defaults of 
                            Nothing -> return []
                            Just (tps, info) ->
                               let op result tp = 
                                      do let sub = singleSubstitution i tp
                                         b <- entailsList [] [ sub |-> x | (x, _) <- ts ]
                                         return $ if b then (tp, info) : result else result
                               in foldM op [] (reverse tps)
                   in mapM (f . fst) ts
                    
               case [ x | x:_ <- candidates ] of
                  (tp, info) : rest | all (tp ==) (map fst rest) -> 
                     do solveConstraint ( TVar i .==. tp $ info )
                        makeConsistent -- ??
                        return []
                  
                  _ -> return ts
      
ambiguousLabel :: ErrorLabel
ambiguousLabel = ErrorLabel "ambiguous predicate" 

missingInSignatureLabel :: ErrorLabel
missingInSignatureLabel = ErrorLabel "predicate missing in signature" 

unresolvedLabel :: ErrorLabel
unresolvedLabel = ErrorLabel "unresolved predicate"

disjointLabel :: ErrorLabel
disjointLabel = ErrorLabel "disjoint predicates"