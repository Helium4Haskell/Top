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
import Data.List (partition)
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
      
      -- try to use a defaulting directive before reporting an error message
      ambiguous (t@(Predicate _ (TVar i), _) : ts) =
         let test (Predicate _ tp', _) = TVar i == tp'
             (ts1, ts2) = partition test ts
         in do defaults   <- tiGets (defaultDirectives . typeclassDirectives)
               candidates <- 
                  let f (Predicate cn _) = 
                         case lookup cn defaults of 
                            Nothing -> return []
                            Just (tps, info) ->
                               let op result tp = 
                                      do let sub = singleSubstitution i tp
                                         b <- entailsList [] [ sub |-> x | (x, _) <- t:ts1 ]
                                         return $ if b then (tp, info) : result else result
                               in foldM op [] (reverse tps)
                  in mapM (f . fst) (t:ts1)
               
               case [ x | x:_ <- candidates ] of
                  (tp, info) : rest | all (tp ==) (map fst rest) -> 
                     do solveConstraint ( TVar i .==. tp $ info )
                        makeConsistent -- ??                     
                  
                  _ ->
                     let f (p, info) = addLabeledError ambiguousLabel (ambiguousPredicate p info)
                     in mapM_ f (t:ts1)
                  
               ambiguous ts2
                   
      ambiguous ((p, info) : ts) =
         do addLabeledError ambiguousLabel (ambiguousPredicate p info)
            ambiguous ts
            
      ambiguous [] = 
         return ()
            
ambiguousLabel :: ErrorLabel
ambiguousLabel = ErrorLabel "ambiguous predicate" 

unresolvedLabel :: ErrorLabel
unresolvedLabel = ErrorLabel "unresolved predicate"

disjointLabel :: ErrorLabel
disjointLabel = ErrorLabel "disjoint predicates"