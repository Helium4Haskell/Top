module Top.Qualifiers.QualifierMap where

import Data.FiniteMap
import Top.States.States (Empty(..))
import Top.Types

---------------------------------------------------------------------
-- Global qualifier map

data GlobalQM q info = 
   GlobalQM
      { globalQualifiers    :: [(q, info)]
      , globalGeneralizedQs :: [(q, info)]
      , globalAssumptions   :: [(q, info)]
      }
     
instance (Show qs, Show info) => Show (GlobalQM qs info) where
   show qm = 
      let f (s, sf)
             | null ps   = []
             | otherwise = ["   " ++ s ++ ": " ++ foldr1 (\x y -> x++", "++y) (map g ps)]
            where ps = sf qm 
          g (p, info) = show p ++ "{" ++ show info ++ "}"
      in unlines $ concatMap f 
            [ ("qualifiers"            , globalQualifiers)
            , ("generalized qualifiers", globalGeneralizedQs)
            , ("assumptions"           , globalAssumptions)
            ]
 
instance Empty (GlobalQM qs info) where
   empty = GlobalQM { globalQualifiers = [], globalGeneralizedQs = [], globalAssumptions = [] }
   
instance Substitutable qs => Substitutable (GlobalQM qs info) where
   sub |-> (GlobalQM as bs cs) = 
      let as' = [ (sub |-> a, info) | (a, info) <- as ]
          bs' = [ (sub |-> b, info) | (b, info) <- bs ]
          cs' = [ (sub |-> c, info) | (c, info) <- cs ]
      in GlobalQM as' bs' cs'
   ftv (GlobalQM as bs cs) = ftv (map fst $ as ++ bs ++ cs) 

---------------------------------------------------------------------
-- Local qualifier map

data LocalQM qs info = LocalQM (FiniteMap Int (GlobalQM qs info))

instance (Show qs, Show info) => Show (LocalQM qs info) where
   show (LocalQM fm) = 
      let f (i, qm) = if null s then "" else "["++show i++"]\n" ++ show qm
             where s = show qm
      in concat (map f (fmToList fm))
   
instance Empty (LocalQM qs info) where
   empty = LocalQM emptyFM
   
instance Substitutable qs => Substitutable (LocalQM qs info) where
   sub |-> LocalQM fm = LocalQM (mapFM (const (sub |->)) fm)
   ftv (LocalQM fm)   = ftv (eltsFM fm)
   
---------------------------------------------------------------------
-- Qualifier map dictionary

data QualifierFlavour = NormalQ | GeneralizedQ | AssumptionQ

data QM_dict f qs info = QM_dict
   { qmGet   :: QualifierFlavour -> Maybe Int -> f qs info -> [(qs, info)]
   , qmSet   :: QualifierFlavour ->       Int -> [(qs, info)] -> f qs info -> f qs info
   }

globalQM :: QM_dict GlobalQM qs info
globalQM = QM_dict 
   { qmGet = \flavour _ -> 
                case flavour of
                   NormalQ      -> globalQualifiers
                   GeneralizedQ -> globalGeneralizedQs
                   AssumptionQ  -> globalAssumptions
   , qmSet = \flavour _ qs m ->
                case flavour of 
                   NormalQ      -> m { globalQualifiers    = qs }
                   GeneralizedQ -> m { globalGeneralizedQs = qs }
                   AssumptionQ  -> m { globalAssumptions   = qs }      
   }

localQM :: QM_dict LocalQM qs info
localQM = QM_dict
   { qmGet = \flavour mInt ->
                case flavour of
                   NormalQ      -> getter mInt globalQualifiers
                   GeneralizedQ -> getter mInt globalGeneralizedQs
                   AssumptionQ  -> getter mInt globalAssumptions
   , qmSet = \flavour int qs (LocalQM fm) -> 
                let qm = lookupWithDefaultFM fm empty int
                in LocalQM (addToFM fm int (qmSet globalQM flavour int qs qm))
   }
 where
   getter Nothing  f (LocalQM fm) = concatMap f (eltsFM fm)
   getter (Just n) f (LocalQM fm) = f (lookupWithDefaultFM fm empty n)

---------------------------------------------------------------------
-- Qualifier map

data QualifierMap qs info = 
   forall f . (Show (f qs info), Substitutable (f qs info)) => 
      QualifierMap (QM_dict f qs info, f qs info)

instance Show (QualifierMap qs info) where
   show (QualifierMap (_, value)) = show value

instance Substitutable qs => Substitutable (QualifierMap qs info) where
   sub |-> QualifierMap (qm, value) = QualifierMap (qm, sub |-> value)
   ftv (QualifierMap (_, value))    = ftv value

makeQualifierMap :: (Substitutable (f qs info), Show (f qs info), Empty (f qs info)) => QM_dict f qs info -> QualifierMap qs info
makeQualifierMap qm = QualifierMap (qm, empty)

getFromQM :: QualifierFlavour -> Maybe Int -> QualifierMap qs info -> [(qs, info)]
getFromQM flavour mInt (QualifierMap (qm, value)) = 
   qmGet qm flavour mInt value

setInQM :: QualifierFlavour -> Int -> [(qs, info)] -> QualifierMap qs info -> QualifierMap qs info
setInQM flavour int qs (QualifierMap (qm, value)) = 
   QualifierMap (qm, qmSet qm flavour int qs value)

addToQM :: QualifierFlavour -> Int -> [(qs, info)] -> QualifierMap qs info -> QualifierMap qs info
addToQM flavour int qs qms = 
   setInQM flavour int (qs ++ getFromQM flavour (Just int) qms) qms

getQualifiers, getGeneralizedQs, getAssumptions :: QualifierMap qs info -> [(qs, info)]
getQualifiers    = getFromQM NormalQ      Nothing
getGeneralizedQs = getFromQM GeneralizedQ Nothing
getAssumptions   = getFromQM AssumptionQ  Nothing

getQualifiersInGroup, getGeneralizedQsInGroup, getAssumptionsInGroup :: Int -> QualifierMap qs info -> [(qs, info)]
getQualifiersInGroup    = getFromQM NormalQ      . Just
getGeneralizedQsInGroup = getFromQM GeneralizedQ . Just
getAssumptionsInGroup   = getFromQM AssumptionQ  . Just

setQualifiersInGroup, setGeneralizedQsInGroup, setAssumptionsInGroup :: Int -> [(qs, info)] -> QualifierMap qs info -> QualifierMap qs info
setQualifiersInGroup    = setInQM NormalQ
setGeneralizedQsInGroup = setInQM GeneralizedQ
setAssumptionsInGroup   = setInQM AssumptionQ

addQualifiersInGroup, addGeneralizedQsInGroup, addAssumptionsInGroup :: Int -> [(qs, info)] -> QualifierMap qs info -> QualifierMap qs info
addQualifiersInGroup    = addToQM NormalQ
addGeneralizedQsInGroup = addToQM GeneralizedQ
addAssumptionsInGroup   = addToQM AssumptionQ