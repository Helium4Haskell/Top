-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  bastiaan@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  portable
-----------------------------------------------------------------------------

module Top.Cobalt.Escape where

data Escape a b = Escape a | Continue b deriving Show

instance Monad (Escape a) where
   return = Continue
   s1 >>= f = 
      case s1 of
         Continue b -> f b
         Escape a   -> Escape a

-- In case they happen to be the same
fromEscape :: Escape a a -> a
fromEscape (Escape x)   = x
fromEscape (Continue x) = x

check :: Maybe b -> a -> Escape a b
check Nothing  x = Escape x
check (Just y) _ = Continue y

forget :: Escape a b -> Maybe b
forget (Escape x)   = Nothing
forget (Continue y) = Just y
      
cond :: Bool -> a -> b -> Escape b a
cond False x y = Escape y
cond True  x y = Continue x

escapeIf :: Bool -> a -> Escape a ()
escapeIf x = continueIf (not x)

continueIf :: Bool -> a -> Escape a ()
continueIf x ev = cond x () ev

-- infixr 4 +++

-- This operator can be used to apply a number of continueIf and escapeIfs in parallel,
-- yielding a list of messages. par is similar. See below for the differences in use.
{-
Old version 
(+++) :: Escape [a] () -> Escape [a] () -> Escape [a] ()
(+++) (Continue _) (Continue _) = Continue ()
(+++) (Escape x)   (Continue _) = Escape x
(+++) (Continue _) (Escape x)   = Escape x
(+++) (Escape x)   (Escape y)   = Escape (x ++ y)
-}

(+++) :: Escape [a] b -> Escape [a] c -> Escape [a] c
(+++) (Continue _) (Continue y) = Continue y
(+++) (Escape x)   (Continue _) = Escape x
(+++) (Continue _) (Escape x)   = Escape x
(+++) (Escape x)   (Escape y)   = Escape (x ++ y)

par :: [(Bool,a)] -> Escape [a] ()
par []         = Continue ()
par ((b,m):xs) = continueIf b [m] +++ par xs

{-
-- For terminating +++ expressions (or use [a] in the final one to prevent this)
endpar :: Escape [a] ()
endpar = Continue ()
-}

escape :: a -> Escape a ()
escape = Escape

testEscape1 = 
  do{ x <- check (Just 2) "Illegal!"
    ; escapeIf (3 < x) "Illegal!"
    ; z <- cond (x < 3) 4 "Illegal!"
    ; check (Just 3) "Illegal!"
    ; escapeIf (z < x) "As it should be"
    ; return ()
    }
    
testEscape2 = 
  do{ par [( 1 < 2, "Not this one" ),
           ( 1 < 1, "This one" ),
           ( 2 < 1, "And this one"),
           ( 3 < 4, "but not this one")
          ]             
    ; return ()
    }

{-    
testEscape3 = 
  do{ continueIf (1 < 2) ["Not this one"] +++
      escapeIf (1 < 1) ["And not this one"] +++
      continueIf (2 < 1) ["This one"] +++
      escapeIf (3 < 4)  ["And this one"] 
    ; return ()
    }
-}

testEscape4 = 
  do{ x <- continueIf (1 < 2) ["Not this one"] +++
      escapeIf (1 < 1) ["And not this one"] +++
      continueIf (2 < 1) ["This one"] +++
      escapeIf (1 < 4)  ["And this one"] +++
      check (Just 'a') ["Bee-bop-a-luba"] +++
      check (Just 'b') ["Gloep!"]
    ; return x
    }
