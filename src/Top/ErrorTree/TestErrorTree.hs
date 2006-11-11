{-# OPTIONS -fglasgow-exts -fallow-overlapping-instances #-}

module Main where

import Top.ErrorTree
import Top.ErrorTree.ErrorTreeInfo
import Top.SolverET
import Top.SolverET.Greedy
import Top.SolverET.TypeGraph
-- Check if there aren't any conflicts between Solver and SolverET:
import Top.Solver.PartitionCombinator
import Top.Solver.SwitchCombinator

import Top.Types
import Top.Constraint
import Top.Constraint.Equality
import Top.Constraint.Information
import Data.Map(Map)

---------------------------------------------------------------------------------------------------

type Info    = ErrorTreeInfo String
type SSolve  = GreedySimple Info
type GSolve  = Greedy Info
type TGSolve = TG Info

instance TypeConstraintInfo Info where

---------------------------------------------------------------------------------------------------
v1,v2,v3,v4,v5,v6,v7,v8,v9,v10 :: Tp
v1 = read "v1"
v2 = read "v2"
v3 = read "v3"
v4 = read "v4"
v5 = read "v5"
v6 = read "v6"
v7 = read "v7"
v8 = read "v8"
v9 = read "v9"
v10 = read "v10"

et1 :: ErrorTree String
et1 = ConstraintNode v1 (v2 .->. v3) 
           (ConstraintNode v3 intType
                 (ErrorNode "v1 is a function to an Int")
                 (ErrorNode "v1 is a function to a non-Int")
           )
           (ConstraintNode v1 (listType v4)
                 (ErrorNode "v1 is a list")
                 (ErrorNode "v1 is neither function nor list")
           )

et2 :: ErrorTree String
et2 = ConstraintNode v1 (boolType .->. v3) 
           (ConstraintNode v3 intType
                 (ErrorNode "E1 -- function from (possible) Bool to (possible) Int")
                 (ErrorNode "E2 -- function from (possible) Bool to non-Int")
           )
           (ConstraintNode v1 (listType v4)
                 (ErrorNode "E3 -- a list")
                 (ErrorNode "E4 -- neither a function on Bools nor a list")
           )

c1,c2,c3,c4,c5,c6,c7,c8,c9,c10 :: EqualityConstraint Info
c1 = v1 .==. (read "v20 -> v21")  $ Right "c1"
c2 = v1 .==. (read "Bool -> v22") $ Right "c2"
c3 = v1 .==. (read "Int -> v23")  $ Right "c3"
c4 = v1 .==. (read "v24 -> Int")  $ Right "c4"
c5 = v1 .==. (read "v25 -> Bool") $ Right "c5"
c6 = v1 .==. (read "Bool -> Int") $ Right "c6"
c7 = v1 .==. (read "Int -> Bool") $ Right "c7"
c8 = v1 .==. (read "[Int]")       $ Right "c8"
c9 = v1 .==. (read "[v26]")       $ Right "c9"
c10 = v1 .==. (read "IO ()")      $ Right "c10"

ec1,ec2,ec3 :: ErrorTreeEqualityConstraint Info
ec1 = ErrorTreeEq (v1 .==. voidType $ Left et1)
ec2 = ErrorTreeEq (v1 .==. voidType $ Left et2)
ec3 = ErrorTreeEq (v1 .==. voidType $ Right "ec3")

---------------------------------------------------------------------------------------------------
-- Lifting to Constraint datatype... phew... 
---------------------------------------------------------------------------------------------------

sc1,sc2,sc3,sc4,sc5,sc6,sc7,sc8,sc9,sc10,sec1,sec2,sec3 :: Constraint SSolve
sc1 = liftConstraint c1
sc2 = liftConstraint c2
sc3 = liftConstraint c3
sc4 = liftConstraint c4
sc5 = liftConstraint c5
sc6 = liftConstraint c6
sc7 = liftConstraint c7
sc8 = liftConstraint c8
sc9 = liftConstraint c9
sc10 = liftConstraint c10
sec1 = liftConstraint ec1
sec2 = liftConstraint ec2
sec3 = liftConstraint ec3
scs = [sc1,sc2,sc3,sc4,sc5,sc6,sc7,sc8,sc9,sc10]

gc1,gc2,gc3,gc4,gc5,gc6,gc7,gc8,gc9,gc10,gec1,gec2,gec3 :: Constraint GSolve
gc1 = liftConstraint c1
gc2 = liftConstraint c2
gc3 = liftConstraint c3
gc4 = liftConstraint c4
gc5 = liftConstraint c5
gc6 = liftConstraint c6
gc7 = liftConstraint c7
gc8 = liftConstraint c8
gc9 = liftConstraint c9
gc10 = liftConstraint c10
gec1 = liftConstraint ec1
gec2 = liftConstraint ec2
gec3 = liftConstraint ec3
gcs = [gc1,gc2,gc3,gc4,gc5,gc6,gc7,gc8,gc9,gc10]

tgc1,tgc2,tgc3,tgc4,tgc5,tgc6,tgc7,tgc8,tgc9,tgc10,tgec1,tgec2,tgec3 :: Constraint TGSolve
tgc1 = liftConstraint c1
tgc2 = liftConstraint c2
tgc3 = liftConstraint c3
tgc4 = liftConstraint c4
tgc5 = liftConstraint c5
tgc6 = liftConstraint c6
tgc7 = liftConstraint c7
tgc8 = liftConstraint c8
tgc9 = liftConstraint c9
tgc10 = liftConstraint c10
tgec1 = liftConstraint ec1
tgec2 = liftConstraint ec2
tgec3 = liftConstraint ec3
tgcs = [tgc1,tgc2,tgc3,tgc4,tgc5,tgc6,tgc7,tgc8,tgc9,tgc10]

---------------------------------------------------------------------------------------------------
-- Constraint solvers:

-- Note: this is cut and paste from Top.ErrorTree.ErrorTree: exporting it from there feels wrong...
toMapSubstitution :: Substitution s => s -> [Int] -> MapSubstitution
toMapSubstitution s vars = let tps = map (\i -> lookupInt i s) vars
                           in listToSubstitution (zip vars tps)

-- NOTE TO STUPID SELF: do not mess with the uniqueCounter -- of course this will cause
-- unwanted equalities between type variables!
solver :: ConstraintSolver constraint Info -> Bool -> [constraint] -> ([Info], Map Int Tp, MapSubstitution)
solver slv defer cs = let opts = solveOptions { setDeferErrorTrees = defer }
                          res  = fst $ solve opts cs slv
                          errs = map fst (errorsFromResult res)
                          fpsub = substitutionFromResult res 
                          FixpointSubstitution fs = fpsub
                          ms = toMapSubstitution fpsub (dom fpsub)
                      in (errs, fs, ms)


solsi,solsd   ::  (Solvable constraint SSolve) =>  [constraint] -> ([Info], Map Int Tp, MapSubstitution)
solgi,solgd   ::  (Solvable constraint GSolve) =>  [constraint] -> ([Info], Map Int Tp, MapSubstitution)
soltgi,soltgd ::  (Solvable constraint TGSolve) => [constraint] -> ([Info], Map Int Tp, MapSubstitution)
solsi  = solver greedySimpleConstraintSolver     False
solgi  = solver greedyConstraintSolver           False
soltgi = solver typegraphConstraintSolverDefault False
solsd  = solver greedySimpleConstraintSolver     True
solgd  = solver greedyConstraintSolver           True
soltgd = solver typegraphConstraintSolverDefault True

fst3 :: (a,b,c) -> a
snd3 :: (a,b,c) -> b
thd3 :: (a,b,c) -> c
fst3 (x,_,_) = x
snd3 (_,y,_) = y
thd3 (_,_,z) = z

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- testing ErrorTrees

test_et1   = evaluateErrorTree noOrderedTypeSynonyms emptySubst                      et2
test_et2 s = evaluateErrorTree stringAsTypeSynonym   (singleSubstitution 1 (read s)) et2
test_et3   = unlines $ map (\s -> "v1 == " ++ s ++ "  -->  " ++ test_et2 s)
             ["v10", "v10->v11", "v10->v11->v12", "(v10->v11)->v12", "v10->Int",
              "v10->Bool", "[v10]", "IO ()", "A v10", "String",
              "Bool->v10", "Bool->v10->v11", "Bool->(v10->v11)"]

----------------------------------------
-- testing ErrorTreeEqualityConstraints and solvers
test_slv1 = fst3 $ solsi [sc1,sc3,sec2,sc2]
test_slv2 = snd3 $ solsi [sc1,sc3,sec2,sc2]
test_slv3 = thd3 $ solsi [sc1,sc3,sec2,sc2]

----------------------------------------
sbuild1 = map (\x -> [x,sec2])
sbuild2 = map (\x -> [sec2,x])
sbuild3 = map (\x -> [sec2,x,x,x,x])
sbuild4 = map (\x -> [x,sec2,sc3,x,x])

gbuild1 = map (\x -> [x,gec2])
gbuild2 = map (\x -> [gec2,x])
gbuild3 = map (\x -> [gec2,x,x,x,x])
gbuild4 = map (\x -> [x,gec2,gc3,x,x])

tgbuild1 = map (\x -> [x,tgec2])
tgbuild2 = map (\x -> [tgec2,x])
tgbuild3 = map (\x -> [tgec2,x,x,x,x])
tgbuild4 = map (\x -> [x,tgec2,tgc3,x,x])

output slv build cs = let xcss = build cs
                          outnosub   = zip  cs 
                                            (map (map fromErrorTreeInfo.fst3.slv) xcss)
                          outwithsub = zip3 cs
                                            (map (map fromErrorTreeInfo.fst3.slv) xcss)
                                            (map (thd3.slv) xcss)
                      in (putStr . unlines . map show) outnosub

test_si1 = output solsi sbuild1 scs 
test_sd1 = output solsd sbuild1 scs 
test_si2 = output solsi sbuild2 scs 
test_sd2 = output solsd sbuild2 scs 
test_si3 = output solsi sbuild3 scs 
test_sd3 = output solsd sbuild3 scs 
test_si4 = output solsi sbuild4 scs 
test_sd4 = output solsd sbuild4 scs 

test_gi1 = output solgi gbuild1 gcs 
test_gd1 = output solgd gbuild1 gcs 
test_gi2 = output solgi gbuild2 gcs 
test_gd2 = output solgd gbuild2 gcs 
test_gi3 = output solgi gbuild3 gcs 
test_gd3 = output solgd gbuild3 gcs 
test_gi4 = output solgi gbuild4 gcs 
test_gd4 = output solgd gbuild4 gcs 

test_tgi1 = output soltgi tgbuild1 tgcs 
test_tgd1 = output soltgd tgbuild1 tgcs 
test_tgi2 = output soltgi tgbuild2 tgcs 
test_tgd2 = output soltgd tgbuild2 tgcs 
test_tgi3 = output soltgi tgbuild3 tgcs 
test_tgd3 = output soltgd tgbuild3 tgcs 
test_tgi4 = output soltgi tgbuild4 tgcs 
test_tgd4 = output soltgd tgbuild4 tgcs 

---------------------------------------------------------------------------------------------------
-- JUNK.... 
myshow :: Tp -> String
myshow (TVar i) = "v" ++ show i
myshow (TCon s) = s
myshow (TApp l r) = "(" ++ myshow l ++ " " ++ myshow r ++ ")" 

{-
-- this is just to test how the option handling works...
tmpsolver :: ConstraintSolver constraint Info -> Bool -> [constraint] -> ([Info], LogEntries)
tmpsolver slv bool cs = let opts = solveOptions { setStopAfterFirstError = bool}
                            res  = fst $ solve opts cs slv
                            errs = map fst (errorsFromResult res)
                            logs = snd $ solve opts cs slv
                        in (errs, logs) 

tmpsol1, tmpsol2 ::  (Solvable constraint SSolve) =>  [constraint] -> ([Info], LogEntries) 
tmpsol1 = tmpsolver greedySimpleConstraintSolver True
tmpsol2 = tmpsolver greedySimpleConstraintSolver False

tst1 = fst (tmpsol1 [sc2,sec2,sc3])
tst2 = fst (tmpsol2 [sc2,sec2,sc3])
-}
