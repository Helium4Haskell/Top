module Top.Qualifiers.Subtypings where

import Top.Qualifiers.Qualifiers
import Top.States.SubtypingState
import Top.States.TIState
import Top.Constraints.TypeConstraintInfo
import Top.Types

instance ( HasST m info
         , HasTI m info
         , TypeConstraintInfo info
         ) => 
           Qualifier m info Subtyping
   where      
      --- entailment
      entails list subtyping@(t1 :<: t2)
         | t1 == t2 = return True
         | subtyping `elem` map fst list = return True
         | otherwise =
              do syns  <- getTypeSynonyms
                 rules <- stGets subtypingRules
                 let allRules   = map (SubtypingRule [] . fst) list ++ rules
                     candidates = applyRulesOnce syns allRules subtyping
                 boolList <- mapM (entailsList list) candidates
                 return (or boolList)
         
applyRulesOnce :: OrderedTypeSynonyms -> SubtypingRules -> Subtyping -> [Subtypings]
applyRulesOnce syns rules (t1 :<: t2) =
   concatMap tryRule rules
 where
   st1, st2 :: Tp
   (st1, st2) = (freezeVariablesInType t1, freezeVariablesInType t2)
 
   tryRule :: SubtypingRule -> [Subtypings]
   tryRule (SubtypingRule premises (ct1 :<: ct2))
      
      -- case 1: no premises: only match left type to get transitivity
      | null premises = 
           case mguWithTypeSynonyms syns st1 ct1 of
              Left _ -> []
              Right (_, sub) -> 
                 [[ changeTypes unfreezeVariablesInType $ sub |-> (ct2 :<: st2) ]]
                 
      -- case 2: with premises: match both left and right type
      | otherwise =
           case mguWithTypeSynonyms syns (tupleType [st1, st2]) (tupleType [ct1, ct2]) of
              Left _ -> []
              Right (_, sub) ->
                 [ changeTypes unfreezeVariablesInType $ sub |-> premises ]