module Top.States.SubtypingState where

import Top.Types
import Top.Qualifiers.QualifierMap
import Top.States.States (Empty(..), IsState(..), Has(..))
import Data.List

-- |A type class for monads that contain a qualifier state.
class Monad m => HasST m info | m -> info where  
   stGet :: m (SubtypingState info)
   stPut :: SubtypingState info -> m ()

stModify :: HasST m info => (SubtypingState info -> SubtypingState info) -> m ()
stModify f = do a <- stGet ; stPut (f a)

stGets :: HasST m info => (SubtypingState info -> a) -> m a
stGets f = do a <- stGet ; return (f a)

data SubtypingState info = 
   SubtypingState 
      { subtypingRules :: SubtypingRules
      , subtypingMap   :: QualifierMap Subtyping info
      }
      
instance Show info => Empty (SubtypingState info) where 
   empty = SubtypingState { subtypingRules = [], subtypingMap = makeQualifierMap globalQM }

instance Show info => Show (SubtypingState info) where
   show state =
      "subtype rules:\n" ++ unlines (map show (subtypingRules state)) ++ "subtypings:\n" ++ show (subtypingMap state)

instance Show info => IsState (SubtypingState info)

instance HasST m info => Has m (QualifierMap Subtyping info) where
   get   = stGets subtypingMap
   put x = stModify (\s -> s { subtypingMap = x })
   
---------------------------------------------------------------------
-- * Subtypings

type Subtypings = [Subtyping]
data Subtyping  = Tp :<: Tp deriving Eq

type SubtypingRules = [SubtypingRule] 
data SubtypingRule  = SubtypingRule Subtypings Subtyping

instance Show Subtyping where
   show (t1 :<: t2) = show t1 ++ " <: " ++ show t2

instance ShowQualifiers Subtyping

instance Substitutable Subtyping where
   sub |-> (t1 :<: t2) = (sub |-> t1) :<: (sub |-> t2)
   ftv (t1 :<: t2)     = ftv t1 `union` ftv t2

instance HasTypes Subtyping where
   getTypes      (t1 :<: t2) = [t1, t2]
   changeTypes f (t1 :<: t2) = (changeTypes f t1) :<: (changeTypes f t2)
   
instance Show SubtypingRule where
   show (SubtypingRule xs x) = 
      show (xs .=>. x)
      
instance ShowQualifiers SubtypingRule

instance Substitutable SubtypingRule where
   sub |-> SubtypingRule xs x = SubtypingRule (sub |-> xs) (sub |-> x)
   ftv (SubtypingRule xs x)   = ftv xs `union` ftv x

instance HasTypes SubtypingRule where
   getTypes      (SubtypingRule xs x) = getTypes xs ++ getTypes x
   changeTypes f (SubtypingRule xs x) = SubtypingRule (changeTypes f xs) (changeTypes f x)
    
declareSubtypingRule :: HasST m info => SubtypingRule -> info -> m ()
declareSubtypingRule rule _ = stModify (\x -> x { subtypingRules = rule : subtypingRules x })