module Main where

import Parsec
import qualified ParsecPrim as Prim
import qualified ParsecToken as P
import ParsecLanguage (haskellStyle, LanguageDef(..))
import Top.Constraints.Constraints
import Top.Types
import Top.Constraints.Constraints
import Top.Constraints.TypeConstraintInfo
import Top.Constraints.ExtraConstraints
import Top.Constraints.Equality
import Top.Constraints.Polymorphism (PolymorphismConstraint(..))
import Top.Solvers.SolveConstraints
import Top.TypeGraph.TypeGraphSolver
import Top.States.States
import Top.States.BasicState
import Top.States.TIState
import Top.States.DependencyState
import Top.States.QualifierState
import Top.States.ImplicitParameterState
import Top.States.SubtypingState
import Top.Solvers.BasicMonad
import Top.Qualifiers.Qualifiers
import Top.Qualifiers.TypeClasses ()
import Top.Qualifiers.Dependencies ()
import Top.Qualifiers.ImplicitParameters ()
import Top.Qualifiers.Subtypings ()
import System (getArgs)
import Data.Char
import Data.List
import Data.FiniteMap
import Utils

---------------------------------------------------------------------
-- * Top logo

logo :: [String]
logo = [ "__ __|"        
       , "  |  _ \\  _ \\"
       , " _|\\___/ .__/"
       , "        _|"
       ]

---------------------------------------------------------------------
-- * Top constraint information

newtype TopInfo = TopInfo [(String, String)]

instance Show TopInfo where 
   show (TopInfo xs)
      | null xs   = "[]"
      | otherwise = snd (last xs)

addTopInfo :: String -> String -> TopInfo -> TopInfo
addTopInfo s1 s2 (TopInfo xs) = TopInfo ((s1, s2) : xs)

instance TypeConstraintInfo TopInfo where
   ambiguousPredicate p    = addTopInfo "ambiguous predicate"  (show p)
   unresolvedPredicate p   = addTopInfo "unresolved predicate" (show p)
   equalityTypePair pair   = addTopInfo "type pair"            (show pair)
   parentPredicate p       = addTopInfo "parent predicate"     (show p)
   escapedSkolems is       = addTopInfo "escaped skolems"      (show is)
   neverDirective tuple    = addTopInfo "never directive"      (show tuple)
   closeDirective tuple    = addTopInfo "close directive"      (show tuple)
   disjointDirective t1 t2 = addTopInfo "disjoint directive"   (show (t1, t2))
   
instance PolyTypeConstraintInfo TopQualifiers TopInfo where
   instantiatedTypeScheme s = addTopInfo "instantiated type scheme" (show s)
   skolemizedTypeScheme s   = addTopInfo "skolemized type scheme" (show s)
   
---------------------------------------------------------------------
-- * Top qualifiers

type TopQualifiers = (Predicates, (Dependencies, (ImplicitParameters, Subtypings)))

class IsTopQualifier a where
   toTopQual :: a -> TopQualifiers
   
instance IsTopQualifier Predicate where
   toTopQual x = ([x], empty)
   
instance IsTopQualifier Dependency where
   toTopQual x = (empty, ([x], empty))

instance IsTopQualifier ImplicitParameter where
   toTopQual x = (empty, (empty, ([x], empty)))

instance IsTopQualifier Subtyping where
   toTopQual x = (empty, (empty, (empty, [x])))
   
---------------------------------------------------------------------
-- * Top constraints

type TopConstraint = ConstraintSum (EqualityConstraint) 
                        (ConstraintSum (PolymorphismConstraint TopQualifiers) (ExtraConstraint TopQualifiers))
                        TopInfo
                 
class IsTopConstraint a where
   toTopCon :: a -> TopConstraint

instance IsTopConstraint (EqualityConstraint TopInfo) where
   toTopCon = SumLeft
   
instance IsTopConstraint (PolymorphismConstraint TopQualifiers TopInfo) where
   toTopCon = SumRight . SumLeft

instance IsTopConstraint (ExtraConstraint TopQualifiers TopInfo) where
   toTopCon = SumRight . SumRight                 
                 
---------------------------------------------------------------------
-- * Top solve monad

type TopExtraState = (DependencyState TopInfo, (ImplicitParameterState TopInfo, SubtypingState TopInfo))
type TopSolve      = TypeGraphX TopInfo TopQualifiers TopExtraState
   
instance HasDep TopSolve TopInfo where
   depGet    = do (_, (_, (_, (x1, _)))) <- getX ; return x1
   depPut x1 = do (a, (b, (c, (_, xr)))) <- getX ; putX (a, (b, (c, (x1, xr))))

instance HasIP TopSolve TopInfo where
   ipGet    = do (_, (_, (_, (_, (x2, _ ))))) <- getX ; return x2
   ipPut x2 = do (a, (b, (c, (x1, (_, xr))))) <- getX ; putX (a, (b, (c, (x1, (x2, xr)))))

instance HasST TopSolve TopInfo where
   stGet    = do (_, (_, (_, (_, (_, x3))))) <- getX ; return x3
   stPut x3 = do (a, (b, (c, (x1, (x2, _))))) <- getX ; putX (a, (b, (c, (x1, (x2, x3)))))

---------------------------------------------------------------------
-- * Top lexer

lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
           ( haskellStyle 
                { reservedOpNames = ["==", "::", "<=", "=>", ":=", "~>", "<:" ] 
                , reservedNames   = ["forall", "Generalize", "Instantiate", "Skolemize", "Implicit",
                                     "Prove", "Assume", "MakeConsistent", "PrintState", "Stop", "ContextReduction",
                                     "Declare", "Enter", "Leave", "Class", "Instance", "Never", "Close", 
                                     "Disjoint", "Default" ]
                })

runLex :: Parser (Constraints TopSolve, Int) -> String -> IO ()
runLex p input
        = run (do { P.whiteSpace lexer
                  ; x <- p
                  ; eof
                  ; return x
                  }) input

---------------------------------------------------------------------
-- * Top parser and main function

main :: IO ()
main = do args <- getArgs
          case args of
             [filename] -> 
                do content <- readFile filename
                   runLex pStatements content
             _ -> do putStrLn "Incorrect number of arguments for topsolver"
                     putStrLn "Usage: topsolver <filename>"

run :: Parser (Constraints TopSolve, Int) -> String -> IO ()
run p input =
   case (parse p "" input) of
      Left err -> 
         do putStr "parse error at "
            print err
      Right (cset, unique) -> 
         let result :: SolveResult TopInfo TopQualifiers TopExtraState
             result  = runTypeGraph standardClasses noOrderedTypeSynonyms unique cset
             -- doAtEnd :: TypeGraphX TopInfo TopQualifiers TopExtraState ()
             --doAtEnd = return () -- makeConsistent >> checkSkolems -- >> doAmbiguityCheck
         in do putStrLn (unlines logo)
               putStrLn (debugFromResult result)
               
               putStrLn . concat $ 
                  "Substitution: " : intersperse ", " (
                     [ show (i, lookupInt i (substitutionFromResult result)) 
                     | i <- dom (substitutionFromResult result) 
                     ])
               
               case errorsFromResult result of
                  [] -> putStrLn "(No errors)"
                  es -> let nice (info, lab) =
                               let TopInfo xs = addTopInfo "label" (show lab) info
                               in "{" ++ concat (intersperse ", " [ a++"="++b | (a, b) <- xs]) ++ "}"
                        in do putStr (unlines (map nice es))
                              putStrLn ("(Failed with "++show (length es)++" errors)")
    
pStatements :: Parser (Constraints TopSolve, Int)
pStatements = 
   do xs <- many pStatement
      let vars = filter (isLower . head) . nub . concatMap (either fst fst) $ xs
          varmap = zip vars [0..]
          g (Left (_,f))   = liftConstraint (f varmap)
          g (Right (_, f)) = f varmap
      return (map g xs, length varmap)

pStatement :: Parser (Either (Result TopConstraint) (Result (Constraint TopSolve)))
pStatement = 
   tryList (map (\m -> m >>= (return . Right)) decl ++ [ pConstraint >>= (return . Left) ])
 where
   decl = [ pOperation, pSubtypingRule, pClassDecl, pInstanceDecl, pNeverDecl
          , pCloseDecl, pDisjointDecl, pDefaultDecl
          ]
          
---------------------------------------------------------------------
-- * Top constraint parser 

pConstraint :: Parser (Result TopConstraint)
pConstraint =
   do f <- tryList $
              change pEquality :
              map change
                 [ pGeneralize, pInstantiate, pExplicit, pSkolemize
                 ] ++
              map change 
                 [ pProve, pAssume, pImplicit
                 ]
      info <- pInfo
      return (f info)
             
 where
   change parser =  
      do g <- parser 
         return $ \info ->
            let (a, b) = g info 
            in (a, toTopCon . b)
      
   pEquality =
      do t1 <- pType
         P.reservedOp lexer "=="
         t2 <- pType
         return $ \info -> 
            ( allTypeConstants t1 ++ allTypeConstants t2
            , \varMap -> Equality (applyVarMap varMap t1) (applyVarMap varMap t2) info
            )
            
   pGeneralize = 
      do sv <- pSigmaVar   
         P.reservedOp lexer ":="
         P.reserved lexer "Generalize"
         (monos, tp) <- P.parens lexer $ 
                           do ms <- P.brackets lexer (commas (P.identifier lexer))
                              P.lexeme lexer (char ',')
                              tp <- pType
                              return (map TCon ms, tp)
         return $ \info ->
            ( sv : allTypeConstants monos ++ allTypeConstants tp
            , \varMap -> Generalize (maybe (-1) id $ lookup sv varMap) (applyVarMap varMap monos, applyVarMap varMap tp) info
            )
            
   pInstantiate = 
      do tp <- pType   
         P.reservedOp lexer ":="
         P.reserved lexer "Instantiate"
         sigma <- P.parens lexer pSigma
         return $ \info ->
            ( allTypeConstants tp ++ either toList allTypeConstants sigma
            , \varMap -> Instantiate (applyVarMap varMap tp) (makeSigma varMap sigma) info
            ) 

   -- explicit instance constraint = instantiate            
   pExplicit = 
      do tp <- pType   
         P.reservedOp lexer "::"
         sigma <- pSigma
         return $ \info ->
            ( allTypeConstants tp ++ either toList allTypeConstants sigma
            , \varMap -> Instantiate (applyVarMap varMap tp) (makeSigma varMap sigma) info
            )
           
   pSkolemize = 
      do tp <- pType   
         P.reservedOp lexer ":="
         P.reserved lexer "Skolemize"
         sigma <- P.parens lexer pSigma
         return $ \info ->
            ( allTypeConstants tp ++ either toList allTypeConstants sigma
            , \varMap -> Skolemize (applyVarMap varMap tp) ([], makeSigma varMap sigma) info
            ) 
            
   pProve = 
      do P.reserved lexer "Prove"
         q <- pQualifierList
         return $ \info ->
            ( allTypeConstants q
            , \varMap -> Prove (applyVarMap varMap q) info
            )
            
   pAssume = 
      do P.reserved lexer "Assume"
         q <- pQualifierList
         return $ \info ->
            ( allTypeConstants q
            , \varMap -> Assume (applyVarMap varMap q) info
            )
            
   pImplicit =
      do t1 <- pType
         P.reservedOp lexer ":="
         P.reserved lexer "Implicit"
         (monos, t2) <- P.parens lexer $ 
                           do ms <- P.brackets lexer (commas (P.identifier lexer))
                              P.lexeme lexer (char ',')
                              tp <- pType
                              return (map TCon ms, tp)
         return $ \info ->
            ( allTypeConstants t1 ++ allTypeConstants monos ++ allTypeConstants t2
            , \varMap -> Implicit (applyVarMap varMap t1) (applyVarMap varMap monos, applyVarMap varMap t2) info
            )

---------------------------------------------------------------------
-- * Top operation parser 
   
pOperation :: Parser (Result (Constraint TopSolve))
pOperation = 
   let ops = [ ("Enter"           , enterGroup)
             , ("Leave"           , do qsInfo <- doContextReduction; (_ :: TopQualifiers) <- removeAnnotation qsInfo ; leaveGroup)
             , ("MakeConsistent"  , makeConsistent) 
             , ("ContextReduction", do qsInfo <- doContextReduction; (_ :: TopQualifiers) <- removeAnnotation qsInfo; return ())
             , ("PrintState"      , printState)
             , ("Stop"            , do printState; s <- getMessages; error $ s ++ "***** Stop reached *****")
             ]
       f (s, a) = do P.reserved lexer s
                     return ([], const (Constraint (a, return True, s)))
   in tryList (map f ops)   

---------------------------------------------------------------------
-- * Top subtyping rule parser 
  
pSubtypingRule :: Parser (Result (Constraint TopSolve))
pSubtypingRule =
   do P.reserved lexer "Declare"
      (xs, x) <- P.parens lexer (pContext pSubtyping pSubtyping)
      info    <- pInfo
      let rule   = SubtypingRule xs x
          vars   = filter (isLower . head) . nub . allTypeConstants $ rule
          varmap = zip vars [0..]
      return $ ([], \_ -> Constraint 
         (declareSubtypingRule (applyVarMap varmap rule) info, return True, "Declare "++show rule))  
    
---------------------------------------------------------------------
-- * Top class/instance declaration parser 

pClassDecl :: Parser (Result (Constraint TopSolve))
pClassDecl = 
   do P.reserved lexer "Class"
      tuple@(supers, className) <- pContext (P.identifier lexer) (P.identifier lexer)
      
      let change :: ClassEnvironment -> ClassEnvironment
          change env = addToFM_C (\(s1,is1) (s2,is2) -> (s1 `union` s2,is1 `union` is2)) env className (supers, [])
      
      return ([], \_ -> Constraint
         (tiModify (\s -> s { classenv = change (classenv s) }), return True, "Class "++show tuple))
  
pInstanceDecl :: Parser (Result (Constraint TopSolve))
pInstanceDecl =
   do P.reserved lexer "Instance"
      tuple@(ps, p@(Predicate className _)) <- pContext pPredicate pPredicate
      
      let vars   = filter (isLower . head) . nub . allTypeConstants $ (ps, p)
          varmap = zip vars [0..]
          tuple' = applyVarMap varmap (p, ps)
          change :: ClassEnvironment -> ClassEnvironment
          change env = addToFM_C (\(s1,is1) (s2,is2) -> (s1 `union` s2,is1 `union` is2)) env className ([], [tuple'])
      
      return ([], \_ -> Constraint
         (tiModify (\s -> s { classenv = change (classenv s) }), return True, "Instance "++show tuple))

pNeverDecl :: Parser (Result (Constraint TopSolve))
pNeverDecl = 
   do P.reserved lexer "Never"
      p    <- pPredicate
      info <- pInfo
      
      let vars   = filter (isLower . head) . nub . allTypeConstants $ p
          varmap = zip vars [0..]
          p'     = applyVarMap varmap p
      
      return ([], \_ -> Constraint 
         (addNeverDirective (p', info), return True, "Never " ++ show p ++ "   : {" ++ show info ++ "}"))

pCloseDecl :: Parser (Result (Constraint TopSolve))
pCloseDecl = 
   do P.reserved lexer "Close"
      s    <- P.identifier lexer
      info <- pInfo
      
      return ([], \_ -> Constraint 
         (addCloseDirective (s, info), return True, "Close " ++ s ++ "   : {" ++ show info ++ "}"))

pDisjointDecl :: Parser (Result (Constraint TopSolve))
pDisjointDecl = 
   do P.reserved lexer "Disjoint"
      ss    <- commas (P.identifier lexer)
      info <- pInfo
      
      return ([], \_ -> Constraint 
         (addDisjointDirective (ss, info), return True, "Disjoint " ++ show ss ++ "   : {" ++ show info ++ "}"))

pDefaultDecl :: Parser (Result (Constraint TopSolve))
pDefaultDecl = 
   do P.reserved lexer "Default"
      className <- P.identifier lexer    
      typeList  <- 
         let single = pType >>= \tp -> return [tp]
             more   = P.parens lexer (commas pType)
         in tryList [more, single]
      info      <- pInfo
      return ([], \_ -> Constraint 
         ( addDefaultDirective (className, (typeList, info))
         , return True
         , "Default " ++ className ++ " (" ++ concat (intersperse "," (map show typeList)) ++ ")   : {" ++ show info ++ "}")
         )
       
---------------------------------------------------------------------
-- * Other parsers 
         
pInfo :: Parser TopInfo
pInfo = tryList [ withInfo, withoutInfo ]
   where
      withInfo =
         do P.reservedOp lexer ":"
            s <- manyTill anyChar (do { char '\n' ; return () } <|> eof)
            P.whiteSpace lexer
            return (TopInfo [("msg", s)])
      withoutInfo =
         do P.reservedOp lexer ";"
            P.whiteSpace lexer
            return (TopInfo [("msg", "<no message>")])

pContext :: Parser a -> Parser b -> Parser ([a], b)
pContext p1 p2 = 
   do as <- tryList [ listContext, singletonContext, emptyContext]
      b  <- p2
      return (as, b)     
 where
   emptyContext = 
      return []
   singletonContext = 
      do a <- p1
         P.reservedOp lexer "=>"  
         return [a]        
   listContext = 
      do as <- P.parens lexer (commas p1)      
         P.reservedOp lexer "=>"
         return as
         
pSigma :: Parser (Either String (Scheme TopQualifiers))
pSigma = try (do s <- pSigmaVar; return (Left s)) 
         <|> (do s <- pTypeScheme; return (Right s))

pSigmaVar :: Parser String
pSigmaVar = do s <- P.identifier lexer
               case s of
                  's' : rest | all isDigit rest -> return s
                  _ -> fail ""

pTypeScheme :: Parser (Scheme TopQualifiers)
pTypeScheme = do qs <- option [] $
                          do P.reserved lexer "forall"
                             xs <- many1 (P.identifier lexer)
                             P.symbol lexer "."
                             return xs
                 (pss, tp) <- pContext pOneQualifier pType 
                 let sub = zip qs [10000..]
                     ps  = foldr plus empty pss
                 return (quantify (map snd sub) (applyVarMap sub ps .=>. applyVarMap sub tp))
 
pQualifierList :: Parser TopQualifiers
pQualifierList = 
   tryList [ P.parens lexer (commas pOneQualifier) >>= (return . foldr plus empty)
           , pOneQualifier
           ]
 
pOneQualifier :: Parser TopQualifiers
pOneQualifier = tryList
   [ pPredicate         >>= (return . toTopQual)
   , pDependency        >>= (return . toTopQual)
   , pImplicitParameter >>= (return . toTopQual)
   , pSubtyping         >>= (return . toTopQual)
   , P.parens lexer pOneQualifier
   ]

pPredicate :: Parser Predicate
pPredicate = 
   do s  <- P.identifier lexer
      tp <- pType2
      return (Predicate s tp)

pDependency :: Parser Dependency
pDependency = 
   do s <- P.identifier lexer
      P.symbol lexer "."
      t1 <- pType
      P.reservedOp lexer "~>"
      t2 <- pType
      return (Dependency s t1 t2)

pImplicitParameter :: Parser ImplicitParameter
pImplicitParameter = 
   do P.reservedOp lexer "?"
      s <- P.identifier lexer
      P.reservedOp lexer "::"
      tp <- pType
      return (ImplicitParameter s tp)

pSubtyping :: Parser Subtyping
pSubtyping = 
   do t1 <- pType
      P.reservedOp lexer "<:"
      t2 <- pType
      return (t1 :<: t2)

pType :: Parser Tp
pType = do left <- pType1
           option left $
             do P.reservedOp lexer "->"
                right <- pType
                return (left .->. right)

pType1 :: Parser Tp
pType1 = do tps <- many1 pType2
            return (foldl1 TApp tps)
      
pType2 :: Parser Tp
pType2 = tryList [
          do s <- P.identifier lexer
             return (TCon s)
        , do tps <- P.parens lexer (commas pType)
             case tps of
                [tp] -> return tp
                _    -> return (tupleType tps)
        , do tp <- P.brackets lexer pType
             return (listType tp)
    ]
---------------------------------------------------------------------
-- * Miscellaneous

type VarMap   = [(String, Int)]
type Result a = ([String], VarMap -> a)

applyVarMap :: HasTypes a => VarMap -> a -> a
applyVarMap varmap = 
   let f tp =
          case tp of
             TApp l r -> TApp (f l) (f r)
             TCon s   -> maybe (TCon s) TVar (lookup s varmap)
             TVar _   -> tp   
   in changeTypes f
   
commas :: Parser a -> Parser [a]
commas  p = p `sepBy` P.lexeme lexer (char ',')

tryList :: [Parser a] -> Parser a 
tryList = foldr1 (<|>) . map try

toList :: a -> [a]
toList a = [a]

makeSigma :: VarMap -> Either String (Scheme TopQualifiers) -> Sigma TopQualifiers
makeSigma vm (Left s)  = let err = internalError "TopSolver.hs" "makeSigma" "sigma var not in variable map" 
                         in SigmaVar (maybe err id $ lookup s vm)
makeSigma vm (Right s) = SigmaScheme (applyVarMap vm s)