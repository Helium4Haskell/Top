-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An equality constraint represents a unification of two types. At the end,
-- the two types should be equivalent.
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
   = Instantiate Tp (Sigma qs)    info   -- or: explicit instance constraint
   | Skolemize Tp (Tps, Sigma qs) info
   | Prove qs                     info
   | Assume qs                    info
   | Implicit Tp (Tps, Tp)        info

-- |The constructor of an instantiate (explicit instance) constraint.
(.::.) :: Tp -> Scheme qs -> info -> ExtraConstraint qs info
tp .::. s = Instantiate tp (SigmaScheme s)

instance (Show info, ShowQualifiers qs, Substitutable qs) => Show (ExtraConstraint qs info) where
   show typeConstraint =
      case typeConstraint of
         Instantiate tp sigma info ->
            show tp ++ " := Instantiate" ++ commaList [show sigma] ++ showInfo info            
         Skolemize tp (monos, sigma) info ->
            show tp ++ " := Skolemize" ++ commaList [show monos, show sigma] ++ showInfo info 
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
         Instantiate tp sigma info      -> Instantiate tp sigma (f info)          
         Skolemize tp pair info         -> Skolemize tp pair (f info)
         Prove p info                   -> Prove p (f info) 
         Assume p info                  -> Assume p (f info) 
         Implicit t1 (monos, t2) info   -> Implicit t1 (monos, t2) (f info)

instance Substitutable qs => Substitutable (ExtraConstraint qs info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Instantiate tp sigma info      -> Instantiate (sub |-> tp) (sub |-> sigma) info         
         Skolemize tp pair info         -> Skolemize (sub |-> tp) (sub |-> pair) info
         Prove p info                   -> Prove (sub |-> p) info
         Assume p info                  -> Assume (sub |-> p) info 
         Implicit t1 (monos, t2) info   -> Implicit (sub |-> t1) (sub |-> monos, sub |-> t2) info
      
   ftv typeConstraint =
      case typeConstraint of
         Instantiate tp sigma _    -> ftv tp `union` ftv sigma         
         Skolemize tp pair _       -> ftv tp `union` ftv pair
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

            Instantiate tp sigma info ->
               let {- hack -}
                   newinfo = case sigma of
                                SigmaScheme x | withoutQuantors x -> instantiatedTypeScheme x info
                                _ -> info
               in 
                  pushConstraint $ liftConstraint 
                     (sigma .<=. tpToSigma tp $ newinfo)
            
            Skolemize tp pair info ->
               let {- hack -}
                   newinfo = case (snd pair) of
                                SigmaScheme x | withoutQuantors x -> skolemizedTypeScheme ([], x) info
                                _ -> info
               in 
                  pushConstraint $ liftConstraint
                     (Subsumption (tpToSigma tp) pair newinfo)
        
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
                        , Subsumption (SigmaVar sv) (monos, tpToSigma t1) info
                        ]
                     
tpToSigma :: Empty qs => Tp -> Sigma qs
tpToSigma = SigmaScheme . noQuantifiers . (empty .=>.)