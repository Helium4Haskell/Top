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
   = Generalize   Int (Tps, Tp)  info
   | Subsumption  (Sigma qs) (Sigma qs) info

-- |The constructor of an equality constraint.
(.<=.) :: Sigma qs -> Sigma qs -> info -> PolymorphismConstraint qs info
(.<=.) = Subsumption

instance (ShowQualifiers qs, Show info, Substitutable qs) => Show (PolymorphismConstraint qs info) where
   show constraint = 
      case constraint of
         Generalize sv (monos, tp) info ->
            "s" ++ show sv ++ " := Generalize" ++ commaList [show (ftv monos), show tp] ++ showInfo info
         Subsumption sigma1 sigma2 info -> 
            show sigma1 ++ " <= " ++ show sigma2 ++ showInfo info
            
    where showInfo info = "   : {" ++ show info ++ "}"
          commaList xs
             | null xs   = par ""
             | otherwise = par (foldr1 (\x y -> x++","++y) xs)
          par s = "("++s++")"

instance Functor (PolymorphismConstraint qs) where
   fmap f constraint =
      case constraint of
         Generalize sv (monos, tp) info -> Generalize sv (monos, tp) (f info)
         Subsumption sigma1 sigma2 info -> Subsumption sigma1 sigma2 (f info)
         
instance Substitutable qs => Substitutable (PolymorphismConstraint qs info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Generalize sv (monos, tp) info -> Generalize sv (sub |-> monos, sub |-> tp) info
         Subsumption sigma1 sigma2 info -> Subsumption (sub |-> sigma1) (sub |-> sigma2) info
         
   ftv typeConstraint =
      case typeConstraint of
         Generalize _ (monos, tp) _  -> ftv monos `union` ftv tp
         Subsumption sigma1 sigma2 _ -> ftv sigma1 `union` ftv sigma2
         
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
               psGenSimple    <- removeAnnotation psGen
               putToProve psNew
               addToGeneralized psGen
               
               tpNewer <- applySubst tpOld -- !! context reduction can extend the substitution
               as <- ftvList psGen
               let finalAlphas = (as `union` ftv (tpNewer)) `intersect` allAlphas
               
               let scheme = quantify finalAlphas (psGenSimple .=>. tpNewer)
               storeTypeScheme var scheme

         Subsumption sigma1 sigma2 info -> 
            do -- left-hand side
               scheme1 <- replaceSchemeVar sigma1
               qtp1    <- instantiateM scheme1
               -- right-hand side
               scheme2 <- replaceSchemeVar sigma2
               qtp2 <- skolemizeTruly scheme2 -- Faked info scheme2
               -- new constraints
               let (ps1, tp1) = split qtp1
                   (ps2, tp2) = split qtp2
               aps1 <- annotate (equalityTypePair (tp1, tp2) $ originalTypeScheme scheme1 info) ps1
               addToProve aps1
               aps2 <- annotate (equalityTypePair (tp1, tp2) $ originalTypeScheme scheme2 info) ps2
               addToAssumptions aps2
               pushConstraint $ liftConstraint
                  (tp1 .==. tp2 $ originalTypeScheme scheme1 info)