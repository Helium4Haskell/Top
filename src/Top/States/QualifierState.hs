module Top.States.QualifierState where

import Top.Types
import Top.States.States
import Data.FiniteMap
import Data.List

-- |A type class for monads that contain a qualifier state.
class Monad m => HasQual m qs info | m -> qs, m -> info where  
   qualGet :: m (QualifierState qs info)
   qualPut :: QualifierState qs info -> m ()

qualModify :: HasQual m qs info => (QualifierState qs info -> QualifierState qs info) -> m ()
qualModify f = do a <- qualGet ; qualPut (f a)

qualGets :: HasQual m qs info => (QualifierState qs info -> a) -> m a
qualGets f = do a <- qualGet ; return (f a)

data QualifierState qs info = 
   QualifierState
      { groupCounter :: Int
      , groupStack   :: [Int]
      , schemeMap    :: FiniteMap Int (Scheme qs)      -- ^ Type scheme map
      }

instance (Substitutable qs, ShowQualifiers qs, Show info) => Show (QualifierState qs info) where
   show st = 
      let f (i, s) = "   s"++show i++" = "++show s
      in unlines $
            [ "group counter: " ++ show (groupCounter st)
            , "group stack: " ++ show (groupStack st)
            , "schememap:"
            ] ++ map f (fmToList $ schemeMap st)
            
instance Empty (QualifierState qs info) where
   empty = QualifierState { groupCounter = 1, groupStack = [0], schemeMap = emptyFM }

instance (Substitutable qs, ShowQualifiers qs, Show info) => IsState (QualifierState qs info)

allTypeSchemes :: HasQual m qs info => m (FiniteMap Int (Scheme qs))
allTypeSchemes = 
   qualGets schemeMap

getTypeScheme :: HasQual m qs info => Int -> m (Scheme qs)
getTypeScheme i =  
   let err = error "sigma var not found in map"
   in qualGets (\s -> lookupWithDefaultFM (schemeMap s) err i)

storeTypeScheme :: HasQual m qs info => Int -> Scheme qs -> m ()
storeTypeScheme sv scheme = 
   qualModify (\s -> s { schemeMap = addToFM (schemeMap s) sv scheme })     
   
replaceSchemeVar :: HasQual m qs info => Sigma qs -> m (Scheme qs)
replaceSchemeVar (SigmaVar i)    = getTypeScheme i
replaceSchemeVar (SigmaScheme s) = return s

-------------------------------------------------------------------
-- Group numbers (0 is the initial group number...)

nextGroupNumber :: HasQual m qs info => m Int
nextGroupNumber = 
   do st <- qualGet
      qualPut st { groupCounter = groupCounter st + 1 }
      return (groupCounter st)
      
enterGroup :: HasQual m qs info => m ()
enterGroup = 
   do n <- nextGroupNumber
      qualModify (\st -> st { groupStack = n : groupStack st } )

leaveGroup :: HasQual m qs info => m ()
leaveGroup = 
   let f []     = [] -- exceptional
       f (_:ns) = ns
   in qualModify (\st -> st { groupStack = f (groupStack st) } )

currentGroup :: HasQual m qs info => m Int
currentGroup = 
   let f []    = 0 -- exceptional: initial group number
       f (n:_) = n
   in qualGets (f . groupStack)