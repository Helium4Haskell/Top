-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-----------------------------------------------------------------------------

module Top.States.BasicState where

import Top.Constraints.Constraints
import Control.Monad
import Utils (internalError)
  
---------------------------------------------------------------------
-- A state for basic constraint solver operations

class Monad m => HasBasic m info | m -> info where 
   basicGet :: m (BasicState m info)
   basicPut :: BasicState m info -> m ()

basicModify :: HasBasic m info => (BasicState m info -> BasicState m info) -> m ()
basicModify f = do a <- basicGet ; basicPut (f a)

basicGets :: HasBasic m info => (BasicState m info -> a) -> m a
basicGets f = do a <- basicGet ; return (f a)

data BasicState m info = BasicState 
   { constraints :: Constraints m
   , debug       :: ShowS
   , errors      :: [(info, m Bool)]
   , conditions  :: [(m Bool, String)]
   }

emptyBasic :: BasicState m info
emptyBasic = BasicState 
   { constraints = []
   , debug       = id
   , errors      = []
   , conditions  = []
   }
       
instance Show (BasicState m info) where 
   show s = unlines $ [ "Constraints"
                      , "-----------"
                      ] ++
                      map (("  - "++) . show) (constraints s) ++
                      [ "("++show (length (constraints s))++" constraints, "
                        ++ show (length (errors s))++" errors, "
                        ++ show (length (conditions s))++" checks)"
                      ]         
   
---------------------------------------------------------------------
-- pushing and popping constraints

pushConstraint  :: HasBasic m info => Constraint m -> m ()
pushConstraints :: HasBasic m info => Constraints m -> m ()
pushOperation   :: HasBasic m info => m () -> m ()
popConstraint   :: HasBasic m info => m (Maybe (Constraint m))
allConstraints  :: HasBasic m info => m (Constraints m)

pushConstraint x   = basicModify (\s -> s { constraints = x : constraints s })
pushConstraints xs = basicModify (\s -> s { constraints = xs ++ constraints s })
pushOperation m    = pushConstraint (Constraint (m, return True, "<operation>"))
popConstraint      = do cs <- allConstraints 
                        case cs of 
                          []     -> return Nothing
                          (x:xs) -> do basicModify (\s -> s { constraints = xs })
                                       return (Just x)
allConstraints     = basicGets constraints  

---------------------------------------------------------------------
-- debugging   
   
printMessage :: HasBasic m info => String -> m ()
getMessages  :: HasBasic m info => m String

printMessage x = basicModify (\s -> s { debug = debug s . (x++) . ("\n"++) })
getMessages    = basicGets (($ []) . debug)
   
---------------------------------------------------------------------
-- errors
 
addError        :: HasBasic m info => info -> m ()
addCheckedError :: HasBasic m info => (info, m Bool) -> m ()   
getErrors       :: HasBasic m info => m [info]   
checkErrors     :: HasBasic m info => m ()

addError x        = addCheckedError (x, return True)
addCheckedError x = basicModify (\s -> s { errors = x : errors s })
getErrors         = basicGets (map fst . errors)
checkErrors = 
   do xs <- basicGets errors
      ys <- filterM snd xs
      basicModify (\s -> s { errors = ys })

---------------------------------------------------------------------
-- conditions

addCheck :: HasBasic m info => String -> m Bool -> m ()
doChecks :: HasBasic m info => m ()

addCheck text check = basicModify (\s -> s { conditions = (check, text) : conditions s})
doChecks = 
   do errs <- getErrors
      when (null errs) $ 
        do ms <- basicGets conditions
           bs <- let f (m, _) = do bool <- m
                                   return (not bool)
                 in filterM f ms
           unless (null bs) $ 
              internalError "Top.States.BasicState" "doChecks"
                ( "\n\n  The following constraints were violated:\n" ++ 
                      unlines (map (("  - "++) . snd) bs)) 
                            
---------------------------------------------------------------------
-- solving constraints

startSolving  :: HasBasic m info => m ()
solveAndCheck :: HasBasic m info => m ()

startSolving = 
   do mc <- popConstraint
      case mc of                    
         Nothing -> return ()
         Just c  -> 
            do solveConstraint c 
               addCheck (show c) (checkCondition c)
               startSolving
                       
solveAndCheck = 
   do startSolving
      doChecks
