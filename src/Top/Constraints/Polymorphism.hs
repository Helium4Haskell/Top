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
   = Generalize   Int        (Tps, Tp)       info
   | Subsumption  (Sigma qs) (Tps, Sigma qs) info

-- |A constructor of a subsumption constraint.
(.<=.) :: Sigma qs -> Sigma qs -> info -> PolymorphismConstraint qs info
s1 .<=. s2 = Subsumption s1 ([], s2)

instance (ShowQualifiers qs, Show info, Substitutable qs) => Show (PolymorphismConstraint qs info) where
   show constraint = 
      case constraint of
         Generalize sv (monos, tp) info ->
            "s" ++ show sv ++ " := Generalize" ++ commaList [show (ftv monos), show tp] ++ showInfo info
         Subsumption sigma1 (monos, sigma2) info -> 
            show sigma1 ++ " <=" ++ 
            (if null monos then " " else show monos ++ " ") ++ 
            show sigma2 ++ showInfo info
            
    where showInfo info = "   : {" ++ show info ++ "}"
          commaList xs
             | null xs   = par ""
             | otherwise = par (foldr1 (\x y -> x++","++y) xs)
          par s = "("++s++")"

instance Functor (PolymorphismConstraint qs) where
   fmap f constraint =
      case constraint of
         Generalize sv pair info      -> Generalize sv pair (f info)
         Subsumption sigma1 pair info -> Subsumption sigma1 pair (f info)
         
instance Substitutable qs => Substitutable (PolymorphismConstraint qs info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Generalize sv (monos, tp) info -> Generalize sv (sub |-> monos, sub |-> tp) info
         Subsumption sigma1 pair info -> Subsumption (sub |-> sigma1) (sub |-> pair) info
         
   ftv typeConstraint =
      case typeConstraint of
         Generalize _ (monos, tp) _  -> ftv monos `union` ftv tp
         Subsumption sigma1 pair _ -> ftv sigma1 `union` ftv pair
         
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

         Subsumption sigma1 (monos, sigma2) info -> 
            do scheme1 <- replaceSchemeVar sigma1
               scheme2 <- replaceSchemeVar sigma2
               
               let rememberScheme1 = if withoutQuantors scheme1 then id else instantiatedTypeScheme scheme1
                   rememberScheme2 = if withoutQuantors scheme2 then id else skolemizedTypeScheme (monos, scheme2)
                   
               -- left-hand side
               qtp1    <- instantiateM scheme1
               -- right-hand side
               qtp2    <- let newinfo = equalityTypePair (_tp, _tp) {- hack -} $ rememberScheme2 info
                              _tp     = snd (split qtp1)
                          in skolemizeFaked newinfo monos scheme2
               -- new constraints
               let (ps1, tp1) = split qtp1
                   (ps2, tp2) = split qtp2
               aps1 <- annotate (equalityTypePair (tp1, tp2) $ rememberScheme1 info) ps1
               addToProve aps1
               aps2 <- annotate (equalityTypePair (tp1, tp2) $ rememberScheme2 info) ps2
               addToAssumptions aps2
               pushConstraint $ liftConstraint
                  (tp1 .==. tp2 $ rememberScheme1 $ rememberScheme2 info)