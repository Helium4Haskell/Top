module Main where

import Top.Types
import Top.Solvers.GreedySolver
import Top.Solvers.SolveConstraints
import Temp
import TempImport

expr :: Expr
expr = Let "i" (Lambda "x" $ Variable "x") (Apply (Variable "i") (Variable "i"))

scomb :: Expr
scomb = Lambda "f" $ Lambda "g" $ Lambda "x" $ Apply (Apply (Variable "f") (Variable "x")) (Apply (Variable "g") (Variable "x")) 

compose :: Expr
compose = Lambda "f" $ Lambda "g" $ Lambda "x" $ Apply (Variable "f") (Apply (Variable "g") (Variable "x"))

twice, twice' :: Expr
twice = Lambda "f" $ Lambda "x" $ Apply (Variable "f") (Apply (Variable "f") (Variable "x"))
twice' = Lambda "f" $ Let "c" compose (Apply (Apply (Variable "c") (Variable "f")) (Variable "f"))

wrong :: Expr
wrong = Lambda "y" (Apply (Apply (Lambda "x" (Variable "x")) (Variable "y")) (Variable "y"))

test :: Expr -> IO ()
test expr =
   let (cset, tp, unique) = sem_Expr expr [] 0
       cset' = hussel cset
       solveResult = runGreedy standardClasses noOrderedTypeSynonyms unique cset' :: SolveResult MyInfo Predicates ()
   in case errorsFromResult solveResult of
         []   -> putStrLn $ show $ generalizeAll $ substitutionFromResult solveResult |-> tp
         errs -> putStrLn $ unlines $ map show errs

main = do{ putStrLn "let i = \\x -> x in i i"; test expr
  			 ; putStrLn "s combinator"; test scomb
				 ; putStrLn "compose function"; test compose
				 ; putStrLn "twice function"; test twice
				 ; putStrLn "twice function with compose"; test twice'
				 ; putStrLn "wrong function"; test wrong
				 }
