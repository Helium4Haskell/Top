module Top.Constraints.Polymorphism where

import Top.Types
import Top.Constraints.Constraints
import Top.Qualifiers.Qualifiers
import Top.Constraints.Equality ( (.==.) )
import Top.Constraints.TypeConstraintInfo
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.States.QualifierState
import Data.List (union, intersect, (\\))

data PolymorphismConstraint qs info
   = Generalize   Int (Tps, Tp) info
   | Instantiate  Tp (Sigma qs) info   -- or: explicit instance constraint
   | Skolemize    Tp (Tps, Sigma qs) info

-- |The constructor of an instantiate (explicit instance) constraint.
(.::.) :: Tp -> Scheme qs -> info -> PolymorphismConstraint qs info
tp .::. s = Instantiate tp (SigmaScheme s)

instance (ShowQualifiers qs, Show info, Substitutable qs) => Show (PolymorphismConstraint qs info) where
   show constraint = 
      case constraint of
         Generalize sv (monos, tp) info ->
            "s" ++ show sv ++ " := Generalize" ++ commaList [show (ftv monos), show tp] ++ showInfo info
         Instantiate tp sigma info ->
            show tp ++ " := Instantiate" ++ commaList [show sigma] ++ showInfo info            
         Skolemize tp (monos, sigma) info ->
            show tp ++ " := Skolemize" ++ commaList [show monos, show sigma] ++ showInfo info 
            
    where showInfo info = "   : {" ++ show info ++ "}"
          commaList xs
             | null xs   = par ""
             | otherwise = par (foldr1 (\x y -> x++","++y) xs)
          par s = "("++s++")"

instance Functor (PolymorphismConstraint qs) where
   fmap f constraint =
      case constraint of
         Generalize sv pair info      -> Generalize sv pair (f info)
         Instantiate tp sigma info    -> Instantiate tp sigma (f info)          
         Skolemize tp pair info       -> Skolemize tp pair (f info)
         
instance Substitutable qs => Substitutable (PolymorphismConstraint qs info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Generalize sv (monos, tp) info -> Generalize sv (sub |-> monos, sub |-> tp) info
         Instantiate tp sigma info      -> Instantiate (sub |-> tp) (sub |-> sigma) info         
         Skolemize tp pair info         -> Skolemize (sub |-> tp) (sub |-> pair) info
         
   ftv typeConstraint =
      case typeConstraint of
         Generalize _ (monos, tp) _ -> ftv monos `union` ftv tp
         Instantiate tp sigma _     -> ftv tp `union` ftv sigma         
         Skolemize tp pair _        -> ftv tp `union` ftv pair
         
instance ( HasBasic m info
         , HasTI m info
         , HasSubst m info
         , HasQual m ps info
         , QualifierList m info ps aps
         , PolyTypeConstraintInfo ps info
         ) => Solvable (PolymorphismConstraint ps info) m where
   solveConstraint constraint =
      case constraint of

         Generalize var (monosOld, tpOld) _ ->
            do makeConsistent
               monosNew <- applySubst monosOld
               tpNew    <- applySubst tpOld
               ps       <- doContextReduction
               
               let someAlphas = ftv tpNew \\ ftv monosNew
               (allAlphas, psGen, psNew) <- doGeneralization (ftv monosNew) someAlphas ps
               psGenSimple <- removeAnnotation psGen
               putToProve psNew
               addToGeneralized psGen
               
               tpNewer <- applySubst tpOld -- !! context reduction can extend the substitution
               as <- ftvList psGen
               let finalAlphas = (as `union` ftv (tpNewer)) `intersect` allAlphas
               
               let scheme = quantify finalAlphas (psGenSimple .=>. tpNewer)
               storeTypeScheme var scheme

         Instantiate tp sigma info ->
            do scheme <- replaceSchemeVar sigma
               let newInfo = instantiatedTypeScheme scheme info
               qtp    <- instantiateM scheme
               let (ps, itp) = split qtp
               aps <- annotate (equalityTypePair (itp, tp) $ newInfo) ps
               addToProve aps
               pushConstraint $ liftConstraint
                  (itp .==. tp $ newInfo)
         
         Skolemize tp (monos, sigma) info -> 
            do scheme <- replaceSchemeVar sigma
               let newInfo = skolemizedTypeScheme (monos, scheme) info
               qtp <- skolemizeFaked (equalityTypePair (tp, tp) $ newInfo) monos scheme
               let (ps, stp) = split qtp
               aps <- annotate (equalityTypePair (tp, tp) $ newInfo) ps
               addToAssumptions aps
               pushConstraint $ liftConstraint
                  (tp .==. stp $ newInfo)