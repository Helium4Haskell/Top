module Top.States.ImplicitParameterState where

import Top.Types
import Top.States.States
import Top.States.QualifierState
import Top.Qualifiers.QualifierMap
import Data.List

---------------------------------------------------------------------
-- * Implicit Parameters

type ImplicitParameters = [ImplicitParameter]
data ImplicitParameter  = ImplicitParameter String Tp deriving Eq

instance ShowQualifiers ImplicitParameter

instance Show ImplicitParameter where
   show (ImplicitParameter s tp) = "?" ++ s ++ " :: " ++ show tp

instance Substitutable ImplicitParameter where
   sub |-> (ImplicitParameter s tp) = ImplicitParameter s (sub |-> tp)
   ftv (ImplicitParameter _ tp)     = ftv tp
  
instance HasTypes ImplicitParameter where
   getTypes      (ImplicitParameter _ tp) = [tp]
   changeTypes f (ImplicitParameter s tp) = ImplicitParameter s (changeTypes f tp)

-- |A type class for monads that contain implicit parameters.
class Monad m => HasIP m info | m -> info where  
   ipGet :: m (ImplicitParameterState info)
   ipPut :: ImplicitParameterState info -> m ()

ipModify :: HasIP m info => (ImplicitParameterState info -> ImplicitParameterState info) -> m ()
ipModify f = do a <- ipGet ; ipPut (f a)

ipGets :: HasIP m info => (ImplicitParameterState info -> a) -> m a
ipGets f = do a <- ipGet ; return (f a)

data ImplicitParameterState info = 
   ImplicitParameterState 
      { implicitParameters :: QualifierMap ImplicitParameter info }
 
addImplicitParameter :: (HasQual m qs info, HasIP m info) => ImplicitParameter -> info -> m ()
addImplicitParameter ip info =
   do n <- currentGroup
      modify (addQualifiersInGroup n [(ip, info)])

instance Show info => Empty (ImplicitParameterState info) where
   empty = ImplicitParameterState { implicitParameters = makeQualifierMap localQM }

instance Show info => Show (ImplicitParameterState info) where
   show state =
      "implicit parameters:\n" ++ show (implicitParameters state)
      
instance Show info => IsState (ImplicitParameterState info)

instance HasIP m info => Has m (QualifierMap ImplicitParameter info) where
   get   = ipGets implicitParameters
   put x = ipModify (\s -> s { implicitParameters = x })