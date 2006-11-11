{-# OPTIONS -fglasgow-exts #-} 
module Top.ErrorTree.ErrorTreeInfo where

import Top.ErrorTree.Interface
import Top.ErrorTree.ErrorTree
import Utils(internalError)

type ErrorTreeInfo i = Either (ErrorTree i) i

fromErrorTreeInfo :: ErrorTreeInfo i -> i
fromErrorTreeInfo (Right i) = i
fromErrorTreeInfo (Left _)  = internalError "Top.ErrorTree.ErrorTreeInfo" "fromErrorTreeInfo"
                              "attempting to extract information from an unevaluated Error Tree"

instance Show i => HasErrorTree (ErrorTreeInfo i) where
    hasErrorTree (Left _)  = True
    hasErrorTree (Right _) = False

    evalErrorTree eval (Left et) = Right (eval et)
    evalErrorTree _    _         = internalError "Top.ErrorTree.ErrorTreeInfo" "evalErrorTree"
                                   "attempting to evaluate a value that is not an ErrorTree"

    modifyErrorTree f (Left et)  = Left (f et)
    modifyErrorTree _ _          = internalError "Top.ErrorTree.ErrorTreeInfo" "modifyErrorTree"
                                   "attempting to modify a value that is not an ErrorTree"

    applyToErrorTree f (Left et) = f et
    applyToErrorTree _ _         = internalError "Top.ErrorTree.ErrorTreeInfo" "applyToErrorTree"
                                   "attempting to apply a function to a value that is not an ErrorTree"

