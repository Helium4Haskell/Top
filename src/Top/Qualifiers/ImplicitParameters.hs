module Top.Qualifiers.ImplicitParameters where

import Top.States.ImplicitParameterState
import Top.States.SubstState
import Top.States.TIState
import Top.Qualifiers.Qualifiers
import Top.Constraints.Equality
import Top.Constraints.Constraints
import Top.Constraints.TypeConstraintInfo
import Data.List
import Control.Monad
import Utils (internalError)

instance ( HasIP m info
         , HasSubst m info
         , HasTI m info
         , TypeConstraintInfo info
         ) => 
           Qualifier m info ImplicitParameter
   where
      -- entailment
      entails xs x = 
         return (x `elem` map fst xs)
      
      -- normalization
      normalizeFixpoint xs =
         let 
             list = groupBy (\x y -> f x == f y) xs
             f (ImplicitParameter s _, _) = s
             bool = any ((>1) . length) list
             
             addEqualities [] = 
                internalError "Top.Qualifiers.ImplicitParameters" "normalizeFixpoint" "list cannot be empty"
             addEqualities (hd@(ImplicitParameter _ t1, _) : rest) =
                do mapM solveConstraint [ t1 .==. t2 $ info | (ImplicitParameter _ t2, info) <- rest ]
                   return hd
         in   
            do new <- mapM addEqualities list
               when bool makeConsistent -- ??
               return (new, bool)
               
      -- generalization
      generalizeOrNot _ _ =
         return True