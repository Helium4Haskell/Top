module Top.States.DependencyState where

import Top.Types
import Top.States.States
import Top.Qualifiers.QualifierMap
import Data.List

-- |A type class for monads that contain a type inference state.
class Monad m => HasDep m info | m -> info where  
   depGet :: m (DependencyState info)
   depPut :: DependencyState info -> m ()

depModify :: HasDep m info => (DependencyState info -> DependencyState info) -> m ()
depModify f = do a <- depGet ; depPut (f a)

depGets :: HasDep m info => (DependencyState info -> a) -> m a
depGets f = do a <- depGet ; return (f a)

data DependencyState info = 
   DependencyState 
      { dependencyMap :: QualifierMap Dependency info }

instance Show info => Empty (DependencyState info) where
   empty = DependencyState { dependencyMap = makeQualifierMap globalQM }

instance Show info => Show (DependencyState info) where
   show state =
      "dependency map:\n" ++ show (dependencyMap state)

instance Show info => IsState (DependencyState info)

instance HasDep m info => Has m (QualifierMap Dependency info) where
   get   = depGets dependencyMap
   put x = depModify (\s -> s { dependencyMap = x })

---------------------------------------------------------------------
-- * Functional Dependencies

type Dependencies = [Dependency]
data Dependency = Dependency String Tp Tp deriving Eq

instance ShowQualifiers Dependency

instance Show Dependency where
   show (Dependency s t1 t2) = s++"."++show t1++" ~> "++show t2

instance Substitutable Dependency where
   sub |-> (Dependency s t1 t2) = Dependency s (sub |-> t1) (sub |-> t2)
   ftv (Dependency _ t1 t2) = ftv t1 `union` ftv t2
  
instance HasTypes Dependency where
   getTypes      (Dependency _ t1 t2) = [t1, t2]
   changeTypes f (Dependency s t1 t2) = Dependency s (changeTypes f t1) (changeTypes f t2)