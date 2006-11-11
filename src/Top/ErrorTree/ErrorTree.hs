{-# OPTIONS #-}
module Top.ErrorTree.ErrorTree 
     ( ErrorTree(..)
     , evaluateErrorTree  
     ) where

import Top.Types
import Data.List(union)

-- TODO: - naming: evaluateErrorTree vs evalErrorTree vs evalET

---------------------------------------------------------------------------------------------------
-- Datatype for Error Trees
-- Substitutable instance for Error Trees
-- Evaluating an Error Tree (based on type synonyms and an initial substitution)

data ErrorTree info = ConstraintNode Tp Tp (ErrorTree info) (ErrorTree info)
                    | ErrorNode info 

instance Show info => Show (ErrorTree info) where
    show = showErrorTree

showErrorTree :: Show i => ErrorTree i -> String
showErrorTree = unlines . indent 6 . showET
    where showET :: Show i => ErrorTree i -> [String]
          showET (ConstraintNode t1 t2 l (ErrorNode i)) =
                                  let cn = show t1 ++ " == " ++ show t2 ++ " :  "
                                  in (cn ++ show i) : showET l
          showET (ConstraintNode t1 t2 l r) =
                                  let cn = show t1 ++ " == " ++ show t2 ++ " :"
                                  in cn : (indent 4 (showET r) ++ showET l)
          showET (ErrorNode i)  = [show i]
          indent n ss = map (replicate n ' ' ++) ss

---------------------------------------------------------------------------------------------------

instance Substitutable (ErrorTree info) where
    s |-> ConstraintNode t1 t2 l r = ConstraintNode (s|->t1) (s|->t2) (s|->l) (s|->r)
    s |-> ErrorNode i              = ErrorNode i
    ftv (ConstraintNode t1 t2 l r) = ftv t1 `union` ftv t2 `union` ftv l `union` ftv r
    ftv (ErrorNode i)              = []


evaluateErrorTree :: Substitution s => OrderedTypeSynonyms -> s -> ErrorTree info -> info
evaluateErrorTree synonyms subst et = eval mapsubst et where
    mgu      = mguWithTypeSynonyms synonyms
    mapsubst = toMapSubstitution subst (ftv et)
    eval s (ConstraintNode t1 t2 succ fail) = case mgu (s|->t1) (s|->t2) of
                                                Right (_,newsub) -> eval (newsub@@s) succ
                                                Left  _          -> eval s fail
    eval s (ErrorNode info)                 = info 


toMapSubstitution :: Substitution s => s -> [Int] -> MapSubstitution
toMapSubstitution s vars = let tps = map (\i -> lookupInt i s) vars
                           in listToSubstitution (zip vars tps)
