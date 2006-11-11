{-# OPTIONS -fglasgow-exts #-}
module Top.ErrorTree.Interface where

import Top.ErrorTree.ErrorTree
import Utils(internalError)
--import Top.Types

---------------------------------------------------------------------------------------------------
-- Bastiaan's suggestion: introduce a typeclass for representing type constraint information that
-- may contain an Error Tree 

-- An alternative to the rank-2 types would be to make HasErrorTree a multi-parameter typeclass
-- that includes the type i stored inside the ErrorTree. I'm not sure what the advantages of that
-- would be, and it would involve changing a lot of type signatures... 

class HasErrorTree info where
    hasErrorTree     ::                                           info -> Bool
    evalErrorTree    :: (forall i. ErrorTree i -> i)           -> info -> info
    modifyErrorTree  :: (forall i. ErrorTree i -> ErrorTree i) -> info -> info
    applyToErrorTree :: (forall i. ErrorTree i -> a)           -> info -> a

    hasErrorTree     = const False 
    evalErrorTree    = internalError modulename "evalErrorTree"    defaulterror 
    modifyErrorTree  = internalError modulename "modifyErrorTree"  defaulterror 
    applyToErrorTree = internalError modulename "applyToErrorTree" defaulterror 

modulename, defaulterror :: String
modulename   = "Top.ErrorTree.Interface"
defaulterror = "this type can never contain an Error Tree"

---------------------------------------------------------------------------------------------------
{-
-- This might be nice to have, but it confuses the typechecker. (If we actually try to
-- use such an instance it requires the -fallow-incoherent-instances flag...)
--
-- In the end, we only need an instance "Substitutable (ErrorTreeEqualityConstraint info)",
-- which is defined in Top.ErrorTree.Constraint.

instance HasErrorTree info => Substitutable info where
    s |-> i | hasErrorTree i = modifyErrorTree (s|->) i
            | otherwise      = i
    ftv i   | hasErrorTree i = applyToErrorTree ftv i
            | otherwise      = []
-}
