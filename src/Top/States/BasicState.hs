-----------------------------------------------------------------------------
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An interface for a monad that constains the most basic operations to 
-- solve constraints. Can be reused for all kinds of constraint-based
-- analyses.
--
-----------------------------------------------------------------------------

module Top.States.BasicState where

import Top.Constraints.Constraints
import Control.Monad
import Utils (internalError)
  
---------------------------------------------------------------------
-- * A basic state

-- |The type class HasBasic has two parameters: a monad m that contains a 
-- BasicState, and the information that is additionally stored with each 
-- constraint. Two operations should be provided for the monad m: how two
-- get and how to put a BasicState in the monad.
class Monad m => HasBasic m info | m -> info where 
   basicGet :: m (BasicState m info)
   basicPut :: BasicState m info -> m ()

-- |Modify the BasicState contained by the monad.
basicModify :: HasBasic m info => (BasicState m info -> BasicState m info) -> m ()
basicModify f = do a <- basicGet ; basicPut (f a)

-- |Get a value from the current BasicState.
basicGets :: HasBasic m info => (BasicState m info -> a) -> m a
basicGets f = do a <- basicGet ; return (f a)

-- |A BasicState is parameterized over the monad in which the constraints can
-- be solved, and over the information that is stored with each constraint.
data BasicState m info = BasicState 
   { constraints :: Constraints m          -- ^ A stack of constraints that is to be solved
   , debug       :: ShowS                  -- ^ All the debug information
   , errors      :: [info]                 -- ^ The reported errors
   , conditions  :: [(m Bool, String)]     -- ^ Conditions to check (for the solved constraints) 
   }

-- |An empty BasicState.
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
-- * Pushing and popping constraints

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
-- * Debugging

-- |Add one message (String) for debuggin purposes to the current state.   
printMessage :: HasBasic m info => String -> m ()
getMessages  :: HasBasic m info => m String

printMessage x = basicModify (\s -> s { debug = debug s . (x++) . ("\n"++) })
getMessages    = basicGets (($ []) . debug)
   
---------------------------------------------------------------------
-- * Errors
 
-- |With each constraint, additional information is associated. This extra
-- information can be reported if the constraint could not be satisfied.
addError     :: HasBasic m info => info -> m ()
getErrors    :: HasBasic m info => m [info]   
updateErrors :: HasBasic m info => (info -> m info) -> m ()

addError x = basicModify (\s -> s { errors = x : errors s })
getErrors  = basicGets errors
updateErrors f =  
   do errors    <- getErrors
      newErrors <- mapM f errors
      basicModify (\s -> s { errors = newErrors })
      
---------------------------------------------------------------------
-- * Conditions

-- |Add a condition that can be checked afterwards. The first argument is a message to
-- be reported if the condition does not hold.
addCheck :: HasBasic m info => String -> m Bool -> m ()
-- |Check all the conditions in the state. If there is a condition that does not hold, then
-- an internal error is reported. 
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
-- * Solving constraints

-- |Solve all the constraints. Keep popping constraints from the constraint stack
-- until the stack is empty. A popped constraint is solved, and a condition is added
-- to the state. The conditions are not checked for!
startSolving  :: HasBasic m info => m ()
-- |Solve the constraints, and, in the end, check all the conditions.
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
