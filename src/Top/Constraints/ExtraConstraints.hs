-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Some additional constraints.
--
-----------------------------------------------------------------------------

module Top.Constraints.ExtraConstraints where

import Top.Types
import Top.Constraints.Constraints
import Top.Constraints.TypeConstraintInfo
import Top.Qualifiers.Qualifiers
import Top.Constraints.Polymorphism
import Top.States.States
import Top.States.TIState
import Top.States.SubstState
import Top.States.BasicState
import Top.States.QualifierState
import Data.List

data ExtraConstraint qs           info 
   = Prove qs                     info
   | Assume qs                    info
   | Implicit Tp (Tps, Tp)        info

instance (Show info, ShowQualifiers qs, Substitutable qs) => Show (ExtraConstraint qs info) where
   show typeConstraint =
      case typeConstraint of
         Prove p info ->
            "Prove (" ++ concat (intersperse ", " (showQualifiers p)) ++ ")" ++ showInfo info 
         Assume p info ->
            "Assume (" ++ concat (intersperse ", " (showQualifiers p)) ++ ")" ++ showInfo info 
         Implicit t1 (monos, t2) info ->
            show t1 ++ " := Implicit" ++ commaList [show (map TVar $ ftv monos), show t2] ++ showInfo info
            
    where showInfo info = "   : {" ++ show info ++ "}"
          commaList xs
             | null xs   = par ""   
             | otherwise = par (foldr1 (\x y -> x++","++y) xs)
          par s = "("++s++")"

instance Functor (ExtraConstraint qs) where
   fmap f typeConstraint = 
      case typeConstraint of
         Prove p info                   -> Prove p (f info) 
         Assume p info                  -> Assume p (f info) 
         Implicit t1 (monos, t2) info   -> Implicit t1 (monos, t2) (f info)

instance Substitutable qs => Substitutable (ExtraConstraint qs info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Prove p info                   -> Prove (sub |-> p) info
         Assume p info                  -> Assume (sub |-> p) info 
         Implicit t1 (monos, t2) info   -> Implicit (sub |-> t1) (sub |-> monos, sub |-> t2) info
      
   ftv typeConstraint =
      case typeConstraint of
         Prove p _                 -> ftv p
         Assume p _                -> ftv p
         Implicit t1 (monos, t2) _ -> ftv t1 `union` ftv monos `union` ftv t2

instance ( HasBasic m info
         , HasSubst m info
         , HasTI m info
         , HasQual m qs info
         , QualifierList m info qs aqs
         , PolyTypeConstraintInfo qs info
         ) => 
           Solvable (ExtraConstraint qs info) m 
   where
      solveConstraint typeConstraint =
         case typeConstraint of
            Prove qs info ->       
               do aqs <- annotate info qs
                  addToProve aqs
              
            Assume qs info ->
               do aqs <- annotate info qs
                  addToAssumptions aqs
       
            Implicit t1 (monos, t2) info ->
               let -- to help the type inference process :-)
                   similarType = const :: PolymorphismConstraint qs info -> ExtraConstraint qs info -> PolymorphismConstraint qs info 
               in do sv <- getUnique
                     pushConstraints $ liftConstraints
                        [ Generalize sv (monos, t2) info `similarType` typeConstraint
                        , Instantiate t1 (SigmaVar sv) info
                        ]
                     
tpToSigma :: Empty qs => Tp -> Sigma qs
tpToSigma = SigmaScheme . noQuantifiers . (empty .=>.)