-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Examples.hs : Examples of type constraint sets.
--
-------------------------------------------------------------------------------


module Main where

import Top.Constraints.Constraints
import Top.Constraints.EqualityConstraint
import Top.Constraints.InstanceConstraint
import Top.TypeGraph.DefaultHeuristics
import Top.Types
import Top.TypeGraph.TypeGraphSolver 
import Top.States.TIState
import Data.FiniteMap
import Top.Solvers.SolveConstraints

-------------------------------------------------------------------------------
-- Test functions

-- (5777275 reductions, 9217405 cells, 55 garbage collections) for type graph solver
main :: IO ()
main = 
   let f i = do putStrLn ("*** Set "++show i++" ***") >> setResults !! (i-1)
       setResults = [ testOne set1, testOne set2, testOne set3
                    , testOne set4, testOne set5, testOne set6
                    , testOne set7, testOne set8, testOne set9
                    ]
   in mapM_ f [1..length setResults]

testOne :: Show info => [EqualityConstraint info] -> IO ()
testOne set = let unique   = maximum (0:ftv set) + 1
                  synonyms = noOrderedTypeSynonyms
                  result   = solveTypeGraph defaultHeuristics synonyms unique set
              in do putStrLn (debugFromResult result)
                    putStrLn "--- Errors ---"
                    putStrLn $ unlines $ map show $ errorsFromResult result

-------------------------------------------------------------------------------
-- Two examples of constraint-information:
--    - String 
--    - MyTypeError 

data MyTypeError = MyTypeError Int Tp Tp

instance Show MyTypeError where
   show (MyTypeError i t1 t2) = "#"++show i++" : "++show t1++" == "++show t2
instance Substitutable  MyTypeError where 
   ftv (MyTypeError i t1 t2)     = ftv [t1,t2]
   sub |-> (MyTypeError i t1 t2) = MyTypeError i (sub |-> t1) (sub |-> t2)

infixl 3 <==>
t1 <==> t2 = \i -> Equality t1 t2 (MyTypeError i t1 t2)

fun x xs = foldl TApp (TCon x) xs 
var      = TVar
con x    = fun x []
---------------------------------------------------
--   Examples: ConstraintType sets              
                             

set1 :: [EqualityConstraint String]       -- own example
set2 :: [EqualityConstraint String]       -- example from "A simple approach to finding the cause of non-unifiability: Graeme S. Port"
set3 :: [EqualityConstraint MyTypeError]  -- constraintTypes generated from a type-correct Haskell expression
set4 :: [EqualityConstraint MyTypeError]  -- constraintTypes generated from a ill-typed Haskell expression (small change compared to set3) 
set5 :: [EqualityConstraint String]       -- example from "Finding backtrack pointTypes for intelligent backtracking: P.T.Cox"
set6 :: [EqualityConstraint String]       -- idem
set7 :: [EqualityConstraint String]       -- idem
set8 :: [EqualityConstraint String]       -- idem
set9 :: [EqualityConstraint String]       -- paper

set1 = 
   [ Equality (var 0) (fun "f" [fun "a" []]) "#1"
   , Equality (var 1) (fun "f" [fun "b" []]) "#2"
   , Equality (var 2) (fun "f" [fun "a" []]) "#3"
   , Equality (var 0) (var 1) "#4"
   , Equality (var 1) (var 2) "#5"
   , Equality (var 0) (var 2) "#6"
   ]

set2 = 
   [ Equality (fun "p" [var 0,fun "h" [var 0]]) 
                (fun "p" [fun "f" [fun "a" [],var 2],fun "h" [var 2]])  "#1"
   , Equality (fun "q" [var 0,var 5]) 
                (fun "q" [var 1,fun "b" []])  "#2"
   , Equality (fun "r" [fun "a" [],var 2]) 
                (fun "r" [var 4,var 1]) "#3"
   , Equality (fun "s" [var 1,var 3,var 3]) 
                (fun "s" [fun "f" [var 4,var 1],fun "g" [var 4],fun "g" [var 5]]) "#4" 
   ]

set3 = 
   [ var 4  <==> var 1 .->. var 2 .->. var 3 $ 0
   , var 8  <==> var 5 .->. var 6 .->. var 7 $ 1
   , var 9  <==> var 10 .->. var 11 $ 2
   , var 11 <==> var 12 .->. var 13 $ 3
   , var 14 <==> var 15 .->. var 16 $  4
   , var 16 <==> var 17 .->. var 18 $  5
   , var 20 <==> var 21 .->. var 22 $  6
   , var 23 <==> var 24 .->. var 25 $  7
   , var 25 <==> var 26 .->. var 27 $  8
   , var 22 <==> var 27 .->. var 28 $  9
   , var 19 <==> var 28 .->. var 29 $  10
   , var 30 <==> var 31 .->. var 32 $  11
   , var 32 <==> var 33 .->. var 34 $  12
   , var 29 <==> var 34 .->. var 35 $  13
   , var 35 <==> var 36 $  14
   , var 18 <==> var 36 $  15
   , var 13 <==> boolType $  16
   , var 33 <==> var 6 $  17
   , var 17 <==> var 6 $  18
   , var 10 <==> var 5 $  19
   , var 31 <==> var 2 $  20
   , var 15 <==> var 2 $  21
   , var 21 <==> var 1 $  22
   , var 0  <==> var 3 .->. var 7 .->. var 36 $  23
   , var 30 <==> var 0 $  24
   , var 14 <==> var 0 $  25
   , var 24 <==> floatType $  26
   , var 12 <==> intType $  27
   , var 26 <==> listType (var 37) $  28
   , var 19 <==> listType (var 38) .->. listType (var 38) .->. listType (var 38) $  29
   , var 9  <==> intType .->. intType .->. boolType  $  30
   , var 8  <==> var 39 .->.  listType (var 39) .->. listType (var 39) $  31 
   , var 4  <==> var 40 .->.  listType (var 40) .->. listType (var 40) $  32 
   , var 23 <==> var 41 .->. listType (var 41) .->. listType (var 41) $  33
   , var 20 <==> var 42 .->. listType (var 42) .->. listType (var 42) $  34
   ] 

set4 = 
   [ var 4  <==> var 1 .->. var 2 .->. var 3 $  0
   , var 8  <==> var 5 .->. var 6 .->. var 7 $  1
   , var 9  <==> var 10 .->. var 11 $  2
   , var 11 <==> var 12 .->. var 13 $  3
   , var 14 <==> var 15 .->. var 16 $  4
   , var 16 <==> var 17 .->. var 18 $  5
   , var 20 <==> var 21 .->. var 22 $  6
   , var 23 <==> var 24 .->. var 25 $  7
   , var 25 <==> var 26 .->. var 27 $  8
   , var 22 <==> var 27 .->. var 28 $  9
   , var 19 <==> var 28 .->. var 29 $  10
   , var 30 <==> var 31 .->. var 32 $  11
   , var 32 <==> var 33 .->. var 34 $  12
   , var 29 <==> var 34 .->. var 35 $  13
   , var 35 <==> var 36 $  14
   , var 18 <==> var 36 $  15
   , var 13 <==> boolType $  16
   , var 31 <==> var 6 $  17
   , var 17 <==> var 6 $  18
   , var 10 <==> var 5 $  19
   , var 33 <==> var 2 $  20
   , var 15 <==> var 2 $  21
   , var 21 <==> var 1 $  22
   , var 0  <==> var 3 .->. var 7 .->. var 36 $  23
   , var 30 <==> var 0 $  24
   , var 14 <==> var 0 $  25
   , var 24 <==> floatType $  26
   , var 12 <==> intType $  27
   , var 26 <==> listType (var 37) $  28
   , var 19 <==> listType (var 38) .->. listType (var 38) .->. listType (var 38) $  29
   , var 9  <==> intType .->. intType .->. boolType $  30
   , var 8  <==> var 39 .->. listType (var 39) .->.  listType (var 39) $  31
   , var 4  <==> var 40 .->. listType (var 40) .->.  listType (var 40) $  32
   , var 23 <==> var 41 .->. listType (var 41) .->. listType (var 41) $  33
   , var 20 <==> var 42 .->. listType (var 42) .->. listType (var 42) $  34
   ]  
   
set5 = 
   [ Equality (fun "P" [fun "A" []])  (fun "P" [var 0]) "#1"
   , Equality (fun "R" [var 0,var 1]) (fun "R" [var 3,var 3]) "#2" 
   , Equality (fun "M" [var 1])       (fun "M" [var 2]) "#3"
   , Equality (fun "T" [var 2,var 5]) (fun "T" [var 4,var 4]) "#4" 
   , Equality (fun "S" [var 5])       (fun "S" [fun "B" []]) "#5"
   ]     	    
  
set6 = 
   [ Equality (fun "F" [var 0]) (fun "G" [var 1]) "#1"
   , Equality (var 0)           (var 1) "#2"
   , Equality (var 1)           (fun "H" [var 0]) "#3"
   , Equality (fun "A" [])      (fun "B" []) "#4"
   ]

set7 = 
   [ Equality (fun "H" [fun "F" [var 1], fun "F" [var 1]]) 
                (fun "H" [var 0,fun "F" [fun "A" []]]) "#1"
   , Equality (fun "G" [var 1,var 2]) 
                (fun "G" [fun "K" [var 0],fun "F" [var 5]]) "#2" 
   , Equality (fun "G" [fun "K" [var 0],fun "K" [var 2]]) 
                (fun "G" [var 4,var 4])  "#3"
   , Equality (fun "G" [var 1,var 5])
                (fun "G" [var 4,var 4]) "#4" 
   , Equality (fun "G" [fun "F" [var 5],fun "K" [var 2]]) 
                (fun "G" [fun "F" [fun "B" []],var 5]) "#5"
   , Equality (fun "H" [var 0,fun "F" [fun "A" []]]) 
                (fun "H" [fun "F" [fun "B" []],fun "F" [var 5]]) "#6"
   ]

set8 = 
   [ Equality (fun "G" [var 7,var 2]) (fun "G" [var 4,fun "F" [var 1,var 1]]) "#1" 
   , Equality (fun "F" [var 1,fun "G" [var 7,var 2]]) (var 3) "#2"
   , Equality (var 3) (fun "F" [fun "H" [var 5],fun "G" [var 0,var 6]]) "#3"
   , Equality (var 3) (var 4) "#4"
   , Equality (var 4) (fun "F" [var 1,var 1]) "#5" 
   ]   

set9 = 
   [ Equality  (var 1)  (var 11) "#1" 
   , Equality  (var 0)  (var 1 .->. var 2)  "#2"
   , Equality  (var 3)  (var 13 .->. var 2) "#3" 
   , Equality  (var 13) (intType) "#4"
   , Equality  (var 4)  (var 5 .->. var 3) "#5"
   , Equality  (var 6)  (var 12 .->. var 5)  "#6" 
   , Equality  (var 12) (boolType) "#7"
   , Equality  (var 7)  (var 10) "#8" 
   , Equality  (var 7)  (var 9) "#9"
   , Equality  (var 6)  (var 7 .->. var 8) "#10"
   , Equality  (var 11) (var 8) "#11"
   , Equality  (var 10) (var 8) "#12"
   , Equality  (var 9)  (boolType) "#13"
   , Equality  (var 4)  (intType .->. intType .->. intType) "#14"
   ]

set10 = 
   [ Equality (fun "->" [fun "[]" [var 0],fun "[]" [var 2]]) 
                (fun "->" [var 1,var 1])  "#1"
   , Equality (fun "->" [fun "[]" [var 0],var 2])
                (fun "->" [var 1,var 1]) "#2"
   , Equality (fun "->" [var 0,con "Int"]) 
                (fun "->" [fun "[]" [con "Bool"],var 2]) "#3"               
   ]
{-
qest :: IO ()
qest = let unique   = 100
           s        = unitFM "String" (0, \[] -> listType charType)
           synonyms = (fst $ getTypeSynonymOrdering s, s)
           (uniqueAtTheEnd, substitution, predicates, errors, ioDebug) = 
              solveTypeGraph synonyms unique tb6
       in do putStrLn "--- Constraints ---"
             putStrLn $ unlines (map show tb6)
             putStrLn "--- Debug ---"
             putStrLn ioDebug
             putStrLn "--- Errors ---"
             --putStrLn $ unlines (map show errors) -}

infix 1 $::$, $==$
($::$) t1 t2 s = (t1 .::. generalizeAll t2) (const s, const id)
($==$) t1 t2 s =  (t1 .==. t2) s
tb4 :: Constraints (TypeGraph String)
tb4 = 
  [ TVar 19 $::$ ((TVar 0) .->. (TVar 1)) .->. ((TVar 2) .->. (TVar 0)) .->. (TVar 2) .->. (TVar 1)   $ "#1"
  , TVar 46 .::. generalize [] [Predicate "Ord" (TVar 0)] ((TVar 0) .->. (TVar 0) .->. boolType)   $ (const "#2", const id)
  , TVar 9 $::$ listType (TVar 0) .->. intType   $ "#3"
  , TVar 14 $::$ listType (TVar 0) .->. intType   $ "#4"
  , TVar 23 $::$ listType (TVar 0) .->. intType   $ "#5"
  , TVar 21 $::$ ((TVar 0) .->. (TVar 1)) .->. listType (TVar 0) .->. listType (TVar 1)   $ "#6"
  , TVar 40 .::. generalize [] [Predicate "Ord" (TVar 0)] ((TVar 0) .->. (TVar 0) .->. (TVar 0))   $ (const "#7", const id)
  , TVar 42 $::$ intType .->. intType .->. boolType   $ "#8"
  , TVar 41 $==$ TVar 42   $ "#9"
  , TVar 46 $==$ TVar 43   $ "#10"
  , TVar 43 $==$ TVar 41   $ "#11"
  , TVar 39 $::$ intType .->. intType .->. intType   $ "#12"
  , TVar 38 $==$ TVar 39   $ "#13"
  , TVar 40 $==$ TVar 38   $ "#14"
  , TVar 0 $==$ TVar 2 .->. TVar 3 .->. TVar 1   $ "#15"
   , TVar 0 $::$ (listType (TVar 0) .->. intType .->. stringType) .->. listType (TVar 0) .->. stringType   $ "#16"
  , TVar 11 $::$ intType .->. intType .->. (TVar 1)   $ "#17"
  , TVar 13 $::$ intType .->. intType .->. intType   $ "#18"
  , TVar 18 $::$ intType .->. intType .->. intType   $ "#19"
  , TVar 32 $::$ (listType (TVar 0) .->. intType .->. stringType) .->. listType (TVar 0) .->. stringType   $ "#20"
  , TVar 4 $==$ TVar 10   $ "#21"
  , TVar 4 $==$ TVar 15   $ "#22"
  , TVar 4 $==$ TVar 27   $ "#23"
  , TVar 4 $==$ TVar 33   $ "#24"
  , TVar 4 $==$ TVar 37   $ "#25"
  , TVar 5 $==$ TVar 24   $ "#26"
  , TVar 4 $==$ TVar 2   $ "#27"
  , TVar 5 $==$ TVar 3   $ "#28"
  , TVar 6 $==$ boolType   $ "#29"
  , TVar 25 $==$ TVar 1   $ "#30"
  , TVar 11 $==$ TVar 8 .->. TVar 12 .->. TVar 7   $ "#31"
  , TVar 7 $==$ TVar 6   $ "#32"
  , TVar 9 $==$ TVar 10 .->. TVar 8   $ "#33"
  , TVar 13 $==$ TVar 14 .->. TVar 15 .->. TVar 16 .->. TVar 12   $ "#34"
  , TVar 19 $==$ TVar 18 .->. TVar 20 .->. TVar 17   $ "#35"
  , TVar 17 $==$ TVar 16   $ "#36"
  , TVar 21 $==$ TVar 22 .->. TVar 20   $ "#37"
  , TVar 23 $==$ TVar 24 .->. TVar 22   $ "#38"
  , TVar 28 $==$ TVar 27 .->. TVar 29 .->. TVar 26   $ "#39"
  , TVar 26 $==$ TVar 25   $ "#40"
  , TVar 28 $::$ (TVar 0) .->. listType (TVar 0) .->. listType (TVar 0)   $ "#41"
  , TVar 34 $==$ TVar 31 .->. TVar 35 .->. TVar 30   $ "#42"
  , TVar 30 $==$ TVar 29   $ "#43"
  , TVar 34 $::$ (TVar 0) .->. listType (TVar 0) .->. listType (TVar 0)   $ "#44"
  , TVar 32 $==$ TVar 33 .->. TVar 31   $ "#45"
  , stringType $==$ TVar 35   $ "#46"
  , TVar 36 $==$ boolType   $ "#47"
  , TVar 37 $==$ TVar 1   $ "#48"
  , TVar 36 $::$ boolType   $ "#49"
  ]

tb6 :: Constraints (TypeGraph String)
tb6 = 
  [ TVar 59 $==$ TVar 56   $ "infix application"
  , TVar 56 $==$ TVar 54   $ "right-hand side"
  , TVar 54 $==$ TVar 55   $ "right hand side"
  , TVar 55 $::$ stringType .->. stringType .->. boolType   $ "explicitly typed binding"
  , TVar 0 $==$ TVar 2 .->. TVar 1   $ "function bindings (INTERNAL ERROR)"
  , TVar 5 $==$ TVar 4   $ "element of pattern list"
  , listType (TVar 4) $==$ TVar 3   $ "pattern list"
  , TVar 6 $::$ listType (TVar 0)   $ "constructor"
  , TVar 6 $==$ TVar 1   $ "right-hand side"
  , TVar 3 $==$ TVar 2   $ "pattern of function binding"
  , TVar 9 $==$ TVar 8   $ "element of pattern list"
  , TVar 10 $==$ TVar 8   $ "element of pattern list"
  , listType (TVar 8) $==$ TVar 7   $ "pattern list"
  , TVar 26 $==$ TVar 27 .->. TVar 28 .->. TVar 25   $ "application"
  , TVar 24 $==$ TVar 25 .->. TVar 23   $ "application"
  , TVar 22 $==$ TVar 23 .->. TVar 21  $  "application"
  , TVar 20 $==$ TVar 19 .->. TVar 21 .->. TVar 18  $  "infix application"
  , TVar 18 $==$ TVar 17   $ "infix application (INTERNAL ERROR)"
  , TVar 16 $==$ TVar 17 .->. TVar 29 .->. TVar 15 $   "application"
  , TVar 14 $==$ TVar 13 .->. TVar 15 .->. TVar 12  $  "infix application"
  , TVar 12 $==$ TVar 11   $ "infix application (INTERNAL ERROR)"
  , TVar 11 $==$ TVar 1   $ "right-hand side"
  , TVar 7 $==$ TVar 2   $ "pattern of function binding"
  , TVar 9 $==$ TVar 13   $ "variable"
  , TVar 9 $==$ TVar 27   $ "variable"
  , TVar 10 $==$ TVar 28   $ "variable"
  , TVar 10 $==$ TVar 29   $ "variable"
  , TVar 31 $::$ TVar 0 .->. listType (TVar 0) .->. listType (TVar 0)  $  "pattern constructor"
  , TVar 34 $::$ TVar 0 .->. listType (TVar 0) .->. listType (TVar 0)   $ "pattern constructor"
  , TVar 34 $==$ TVar 35 .->. TVar 36 .->. TVar 33  $  "infix pattern application"
  , TVar 31 $==$ TVar 32 .->. TVar 33 .->. TVar 30  $  "infix pattern application"
  , TVar 44 $::$ TVar 0 .->. listType (TVar 0) .->. listType (TVar 0)   $ "constructor"
  , TVar 44 $==$ TVar 43 .->. TVar 45 .->. TVar 42  $  "infix application"
  , TVar 42 $==$ TVar 41   $ "infix application (INTERNAL ERROR)"
  , TVar 40 $==$ TVar 41 .->. TVar 39  $  "application"
  , TVar 52 $::$ TVar 0 .->. listType (TVar 0) .->. listType (TVar 0)   $ "constructor"
  , TVar 52 $==$ TVar 51 .->. TVar 53 .->. TVar 50   $ "infix application"
  , TVar 50 $==$ TVar 49   $ "infix application (INTERNAL ERROR)"
  , TVar 48 $==$ TVar 49 .->. TVar 47   $ "application"
  , TVar 46 $==$ TVar 39 .->. TVar 47 .->. TVar 38   $ "infix application"
  , TVar 38 $==$ TVar 37   $ "infix application (INTERNAL ERROR)"
  , TVar 37 $==$ TVar 1   $ "right-hand side"
  , TVar 30 $==$ TVar 2   $ "pattern of function binding"
  , TVar 32 $==$ TVar 43   $ "variable"
  , TVar 32 $==$ TVar 51   $ "variable"
  , TVar 35 $==$ TVar 45   $ "variable"
  , TVar 36 $==$ TVar 53   $ "variable"
  , TVar 0 $::$ listType (listType (stringType)) .->. listType (stringType)   $ "explicitly typed binding"
  , TVar 22 $::$ stringType .->. stringType .->. boolType   $ "variable"
  , TVar 40 $::$ listType (listType (stringType)) .->. listType (stringType)  $  "variable"
  , TVar 48 $::$ listType (listType (stringType)) .->. listType (stringType)   $ "variable"
  , TVar 14 $::$ listType (TVar 0) .->. listType (TVar 0) .->. listType (TVar 0)   $ "variable"
  , TVar 46 $::$ listType (TVar 0) .->. listType (TVar 0) .->. listType (TVar 0)   $ "variable"
  , TVar 20 $::$ (TVar 0 .->. TVar 1) .->. (TVar 2 .->. TVar 0) .->. TVar 2 .->. TVar 1   $ "variable"
  , TVar 59 .::. generalize [] [Predicate "Eq" (TVar 0)] (TVar 0 .->. TVar 0 .->. boolType)   $ (const "variable", const id)
  , TVar 26 $::$ listType (listType (TVar 0)) .->. listType (TVar 0)   $ "variable"
  , TVar 16 $::$ (TVar 0 .->. boolType) .->. listType (TVar 0) .->. listType (TVar 0)   $ "variable"
  , TVar 19 $::$ boolType .->. boolType   $ "variable"
  , TVar 24 $::$ listType (stringType) .->. listType (charType)   $ "variable"
  ]
