module Top.Qualifiers.Dependencies where

import Top.Types
import Top.States.SubstState
import Top.States.TIState
import Top.States.DependencyState
import Top.Qualifiers.Qualifiers
import Top.Qualifiers.QualifierMap
import Top.Constraints.TypeConstraintInfo
import Data.List
import Control.Monad (when)
import Utils (internalError)
import Top.Constraints.Constraints
import Top.Constraints.Equality

instance ( HasSubst m info
         , HasTI m info
         , HasDep m info
         , TypeConstraintInfo info
         ) => 
           Qualifier m info Dependency
   where
      --- entailment
      entails ds fdep =
         return (fdep `elem` map fst ds)

      -- normalization
      normalizeFixpoint fdeps = 
         do xss     <- mapM solveOne fdeps
            (ys, b) <- simplifySet (concat xss)
            return (ys, any null xss || b)

       where
         -- apply dependencies
         solveOne pair@(Dependency s t1 t2, info) =
            do syns <- getTypeSynonyms
               deps <- depGets (getAssumptions . dependencyMap)
               let t1Skol = freezeVariablesInType t1
                   list   = [ (a, b) | (Dependency s' a b, _) <- deps, s == s' ]
                   candidates =
                      let f (pt1, pt2) = 
                             case mguWithTypeSynonyms syns t1Skol pt1 of
                                Left _         -> []
                                Right (_, sub) -> [ unfreezeVariablesInType (sub |-> pt2) ]
                      in concatMap f list
               case candidates of
               
                  [] -> -- no candidate yet
                     return [pair]
                     
                  [ctp] -> -- one candidate
                     do solveConstraint (ctp .==. t2 $ info)
                        makeConsistent -- ??
                        return []
                     
                  _ -> -- inconsistency in the dependency relation
                     internalError "Top.Qualifiers.Dependencies" "normalizeFixpoint" "inconsistency in the dependency relation"
         
         -- X.a ~> b and X.a ~> c implies b == c
         simplifySet ys =
            let 
                list = groupBy (\x y -> f x == f y) ys
                f (Dependency s t _, _) = (s, t)
                bool = any ((>1) . length) list
                
                addEqualities [] =
                   internalError "Top.Qualifiers.Dependencies" "normalizeFixpoint" "list cannot be empty"
                addEqualities (hd@(Dependency _ _ t1, _) : rest) =
                   do mapM solveConstraint [ t1 .==. t2 $ info | (Dependency _ _ t2, info) <- rest ]
                      return hd
            in 
               do xs <- mapM addEqualities list
                  when bool makeConsistent -- ??
                  return (xs, bool)