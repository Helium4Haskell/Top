module Main  where

import Top.Cobalt.ParseRules
import Top.Cobalt.AGSyntax
import Top.Cobalt.Syntax
import Top.Cobalt.Generator
import Top.Types
import Data.Map

{-
ex :: TypeSystem
ex = TypeSystem datas rules
 where
   datas = [ AGData "Expr" "Variable" [("ident", "Identifier")]
           , AGData "Expr" "Apply" [("function", "Expr"),("argument", "Expr")]
           , AGData "Expr" "Lambda" [("ident", "Identifier"),("body", "Expr")]
           , AGData "Expr" "Let" [("ident", "Identifier"), ("decl", "Expr"), ("body", "Expr")]
           ]
   rules = [ruleVar, ruleApp, ruleLam, ruleLet]
   ruleVar = 
      let ps = []
          c  = judge (TermVar "G", TermApp "Variable" [TermVar "x"], TermVar "a")
          cs = [TermApp "instc" [TermVar "a", (TermApp "mylookup" [TermVar "x", TermVar "G"])]]
      in TypeRule "[Var]" (DeductionRule ps c) cs
   ruleApp = 
      let ps = [ judge (TermVar "G", TermVar "e1", TermVar "t1")
						   , judge (TermVar "G", TermVar "e2", TermVar "t2")
               ]
          c  = judge (TermVar "G", TermApp "Apply" [TermVar "e1", TermVar "e2"], TermVar "a")
          cs = [TermApp "eqc" [TermVar "t1", (TermApp "arrow" [TermVar "t2", TermVar "a"])]]
      in TypeRule "[App]" (DeductionRule ps c) cs
   ruleLam =  
      let ps = [judge (TermApp "update" [TermVar "x", TermVar "b", TermVar "G"], TermVar "e", TermVar "t")]
          c  = judge (TermVar "G", TermApp "Lambda" [TermVar "x", TermVar "e"], TermVar "a")
          cs = [TermApp "eqc" [TermVar "a", (TermApp "arrow" [TermVar "b", TermVar "t"])]]
      in TypeRule "[Lam]" (DeductionRule ps c) cs
   ruleLet =  
      let ps = [ judge (TermVar "G", TermVar "e1", TermVar "t1")
               , judge (TermApp "update" [TermVar "x", TermVar "s", TermVar "G"], TermVar "e2", TermVar "t2")
               ]
          c  = judge (TermVar "G", TermApp "Let" [TermVar "x", TermVar "e1", TermVar "e2"], TermVar "a")
          cs = [ TermApp "genc" [TermVar "s", TermVar "G", TermVar "t1"]
               , TermApp "eqc" [TermVar "t2", TermVar "a"]          
               ]
      in TypeRule "[Let]" (DeductionRule ps c) cs

judge (a, b, c) = Judgement a b c
-}

env = [ ("instc"   , generalizeAll $ [Predicate "IsSigmaPreds" (TVar 0)] .=>.  TCon "Type" .->. TVar 0 .->. TCon "String" .->. TCon "Constraint")
      , ("eqc"     , toTpScheme    $ TCon "Type" .->. TCon "Type" .->. TCon "String" .->. TCon "Constraint")
      , ("arrow"   , toTpScheme    $ TCon "Type" .->. TCon "Type" .->. TCon "Type")
      , ("update"  , generalizeAll $ [Predicate "IsSigmaPreds" (TVar 0)] .=>. TCon "Identifier" .->. TVar 0 .->. TCon "Gamma" .->. TCon "Gamma")
      , ("mylookup", toTpScheme    $ TCon "Identifier" .->. TCon "Gamma" .->. TCon "TpScheme")
      , ("genc"    , toTpScheme    $ TCon "SVar" .->. TCon "Gamma" .->. TCon "Type" .->. TCon "String" .->. TCon "Constraint")
      ]

classEnv :: ClassEnvironment
classEnv = addToFM standardClasses "IsSigmaPreds"
   ([], [ (Predicate "IsSigmaPreds" (TCon s), []) | s <- ["Type", "TpScheme", "SVar"]])

test file = do{ input <- readFile file             
              ; case run pTypeSystem input of 
							    Just ts -> generator (listToFM env) classEnv ts
							    Nothing -> error "nothing to be done"
				      }

main = test "HM.type"
