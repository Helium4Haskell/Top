module Top.States.States where

---------------------------------------------------------------------
-- * A type class for states.

class (Empty a, Show a) => IsState a where
   showState  :: a -> String
   showStates :: a -> [String]      -- ^ Show this state, and all states that are contained by this state.
                                    -- By default, use the show function from the Show type class.
   showState  = show
   showStates = (:[]) . showState

instance (IsState a, IsState b) => IsState (a, b) where 
   showStates (a,b) = showStates a ++ showStates b
   
instance IsState () where
   showStates () = []
   
------------------------------------------------------------------------
-- * Empty type class

class Empty a where
   empty :: a

instance Empty () where
   empty = ()

instance (Empty a, Empty b) => Empty (a, b) where
   empty = (empty, empty)

instance Empty [a] where
   empty = []

------------------------------------------------------------------------
-- * Plus type class

class Plus a where
   plus :: a -> a -> a

instance Plus () where
   plus () () = ()
   
instance (Plus a, Plus b) => Plus (a, b) where
   plus (a1, b1) (a2, b2) = (a1 `plus` a2, b1 `plus` b2)
   
instance Plus [a] where
   plus as bs = as ++ bs
   
------------------------------------------------------------------------
-- * Has type class

class Monad m => Has m a where
   get :: m a
   put :: a -> m ()
   
gets :: Has m a => (a -> b) -> m b
gets f = get >>= (return . f)

modify :: Has m a => (a -> a) -> m ()
modify f = get >>= (put . f)

add :: (Has m a, Plus a) => a -> m ()
add = modify . plus

instance (Has m a, Has m b) => Has m (a, b) where
   get = do as <- get
            bs <- get
            return (as, bs)
   -- this definition is left-biased: assume that the types 'a' and 'b' are different.
   put (as, bs) = do put as
                     put bs