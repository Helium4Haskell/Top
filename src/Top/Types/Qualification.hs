-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Qualification of types (for instance, predicates to deal with type classes).
--
-----------------------------------------------------------------------------

module Top.Types.Qualification where

import Top.Types.Basics
import Top.Types.Substitution
import Data.List

-----------------------------------------------------------------------------
-- * Qualification

newtype Qualification q a = Qualification ([q], a)

split :: Qualification q a -> ([q], a)
split (Qualification t) = t

infixr 2 .=>.

(.=>.) :: [q] -> a -> Qualification q a 
(.=>.) = curry Qualification

qualifiers :: Qualification q a -> [q]
qualifiers = fst . split

unqualify :: Qualification q a -> a
unqualify = snd . split

qualify :: (Substitutable context, Substitutable q, Substitutable a) => context -> [q] -> a -> Qualification q a
qualify context preds tp = 
   let is  = ftv tp \\ ftv context
       p   = any (`elem` is) . ftv
   in (filter p preds .=>. tp)

showQualifiers :: Show a => [a] -> String
showQualifiers []  = ""
showQualifiers [a] = show a
showQualifiers as  = "(" ++ concat (intersperse ", " (sort (map show as))) ++ ")"

instance (Substitutable q, Substitutable a) => Substitutable (Qualification q a) where
   sub |-> (Qualification t) = Qualification (sub |-> t)
   ftv     (Qualification t) = ftv t

instance (Show q, Show a) => Show (Qualification q a) where
   show (Qualification (ps, a)) = 
      case ps of   
         []  -> show a
         ps  -> showQualifiers ps ++ " => " ++ show a
