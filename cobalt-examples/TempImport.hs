-- ag -dcfsp --module=Temp Temp
--   Shows how to compile a file called Temp.ag
module TempImport where

import Top.Types
import Top.Constraints.Equality
import Top.Constraints.Polymorphism
import Top.Constraints.Constraints hiding (Constraint)
import Top.Solvers.GreedySolver
import Top.Solvers.SolveConstraints
import Top.Qualifiers.TypeClasses
import Top.Constraints.TypeConstraintInfo
import Data.List

type Type       = Tp
type Gamma      = [(Identifier, SigmaPreds)]
type Identifier = String

update    :: IsSigmaPreds a => Identifier -> a -> Gamma -> Gamma
eqc       :: Type -> Type -> String -> Constraint
genc      :: SVar -> Gamma -> Type -> String -> Constraint
instc     :: IsSigmaPreds a => Type -> a -> String -> Constraint
arrow     :: Type -> Type -> Type
mylookup  :: Identifier -> Gamma -> SigmaPreds

update a b c = (a,toSigmaPreds b):c
mylookup a b = maybe (error "mylookup:error") id (lookup a b)
arrow = (.->.)
eqc a b message = SumLeft (Equality a b message)
instc a b message = SumRight (Instantiate a (toSigmaPreds b) message)
genc (SVar a) b c message = SumRight (Generalize a (map TVar (ftv (map snd b)), c) message)


class MakeFresh a where makeFresh :: Int -> a
instance MakeFresh Tp  where makeFresh = TVar
instance MakeFresh SVar where makeFresh i = SVar i
instance IsSigmaPreds SVar where toSigmaPreds (SVar i) = SigmaVar i

data SVar = SVar Int
type MyInfo = String
type Constraint = ConstraintSum EqualityConstraint (PolymorphismConstraint Predicates) MyInfo
instance TypeConstraintInfo MyInfo
instance PolyTypeConstraintInfo Predicates MyInfo

hussel :: [Constraint] -> [Constraint]
hussel = (\(as,bs) -> map snd bs ++ as) . rec [] 
 where
   rec is [] = ([], [])
   rec is (c:rest) = 
      case c of
         SumRight (Instantiate _ (SigmaVar i) _) ->
            let (new, gs) = rec (i:is) rest
                (gs1, gs2) = partition ((`elem` is) . fst) gs
            in (map snd gs2++[c]++new, gs1)
         SumRight (Generalize i _ _)
            | i `elem` is -> let (new, gs) = rec is rest 
                             in (new, (i,c):gs)
         _ -> let (new, gs) = rec is rest 
                  (gs1, gs2) = partition ((`elem` is) . fst) gs
              in (map snd gs2++[c]++new, gs1)
