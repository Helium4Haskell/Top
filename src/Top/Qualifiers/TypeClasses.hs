module Top.Qualifiers.TypeClasses where

import Top.Types
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.Qualifiers.Qualifiers
import Top.Constraints.TypeConstraintInfo

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
         do syns     <- getTypeSynonyms
            classEnv <- getClassEnvironment
         
            let hnf (p, info) =
                   case toHeadNormalForm syns classEnv p of
                      Just qs -> return (zip qs (repeat info))
                      Nothing -> 
                         do addLabeledError unresolvedLabel 
                               (unresolvedPredicate p info)
                            return []
                         
                loop rs [] = rs
                loop rs (x:xs) 
                   | scEntail classEnv (map fst (rs++xs)) (fst x)
                        = loop rs xs
                   | otherwise                    
                        = loop (x:rs) xs
         
            psList <- mapM hnf psNew
            return (loop [] (concat psList))
      
      ambiguousOne (p, info) = 
         addLabeledError ambiguousLabel (ambiguousPredicate p info)

ambiguousLabel :: ErrorLabel
ambiguousLabel = ErrorLabel "ambiguous predicate" 

unresolvedLabel :: ErrorLabel
unresolvedLabel = ErrorLabel "unresolved predicate"