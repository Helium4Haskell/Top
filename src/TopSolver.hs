module Main where

import Parsec
import qualified ParsecToken as P
import ParsecLanguage (haskellStyle, LanguageDef(..))
import Top.Constraints.Constraints
import Top.Types
import Top.Constraints.EqualityConstraint
import Top.Constraints.InstanceConstraint
import Top.Constraints.PredicateConstraint
import Top.Solvers.SolveConstraints
import Top.TypeGraph.TypeGraphSolver
import Top.TypeGraph.DefaultHeuristics
import Top.States.BasicState
import Top.States.SubstState
import Top.States.TIState
import System (getArgs)
import Char
import List

type VarMap   = [(String, Tp)]
type Result   = ([String], VarMap -> Con String)
data Con info = ConEq   (EqualityConstraint  info)
              | ConInst (InstanceConstraint  info)
              | ConPred (PredicateConstraint info)

instance (Monad m, Show info, HasBasic m info, HasSubst m info, HasTI m info) => Solvable (Con info) m where 
   solveConstraint (ConEq x  ) = solveConstraint x
   solveConstraint (ConInst x) = solveConstraint x
   solveConstraint (ConPred x) = solveConstraint x
   checkCondition  (ConEq x  ) = checkCondition x
   checkCondition  (ConInst x) = checkCondition x
   checkCondition  (ConPred x) = checkCondition x

instance Show info => Show (Con info) where
   show (ConEq x  ) = show x
   show (ConInst x) = show x
   show (ConPred x) = show x

class HasConstants a where
   applyVarMap  :: VarMap -> a -> a
   allConstants :: a -> [String]
   
instance HasConstants Tp where 
   applyVarMap varMap tp = 
      case tp of
         TApp l r -> TApp (applyVarMap varMap l) (applyVarMap varMap r)
         TCon s   -> maybe (TCon s) id (lookup s varMap)
         TVar _   -> tp
   allConstants = constantsInType         

instance HasConstants a => HasConstants [a] where
   applyVarMap varMap = map (applyVarMap varMap)
   allConstants       = concatMap allConstants

instance HasConstants Predicate where
   applyVarMap varMap (Predicate s tp) = Predicate s (applyVarMap varMap tp)
   allConstants       (Predicate s tp) = allConstants tp

instance HasConstants QType where
   applyVarMap varMap qtype = 
      let (ps, tp) = split qtype
      in (applyVarMap varMap ps .=>. applyVarMap varMap tp)
      
   allConstants qtype = 
      let (ps, tp) = split qtype
      in allConstants ps ++ allConstants tp
      
instance HasConstants TpScheme where
   applyVarMap varMap (Quantification (is, qmap, qtype)) = Quantification (is, qmap, applyVarMap varMap qtype)
   allConstants = allConstants . unquantify
      
lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
           ( haskellStyle 
                { reservedOpNames = ["==", "::", "<=", "=>"] 
                , reservedNames   = ["forall"]
                })
                
run :: Parser [Result] -> String -> IO ()
run p input
           = case (parse p "" input) of
               Left err -> do{ putStr "parse error at "
                             ; print err
                             }
               Right cs -> 
                  let (xs, ys) = unzip cs
                      vars     = filter (isLower . head) (nub (concat xs))    
                      sub      = zip vars (map TVar [0..])
                      cs'      = map ($ sub) ys
                      result   = solveTypeGraph defaultHeuristics noOrderedTypeSynonyms (length vars) cs'
                  in do putStrLn (debugFromResult result)
                        putStrLn (replicate 50 '-')
                        case errorsFromResult result of
                           [] -> putStrLn "(No errors)" 
                           es -> do putStr (unlines es)
                                    putStrLn ("(Failed with "++show (length es)++" errors)")
                           
                       
                      
runLex :: Parser [Result] -> String -> IO ()
runLex p input
        = run (do { P.whiteSpace lexer
                  ; x <- p
                  ; eof
                  ; return x
                  }) input

main :: IO ()
main = do args <- getArgs
          case args of
             [filename] -> 
                do content <- readFile filename
                   runLex (many pConstraint) content
             _ -> do putStrLn "Incorrect number of arguments for topsolver"
                     putStrLn "Usage: topsolver <filename>"

pConstraint :: CharParser () Result
pConstraint =
   do f    <- try equality <|> try explicit <|> try implicit <|> predicate
      info <- pInfo      
      return (f info)
             
 where
   equality = 
      do t1 <- pType
         P.reservedOp lexer "=="
         t2 <- pType
         return $ \info -> 
            ( allConstants t1 ++ allConstants t2
            , \varMap -> ConEq (Equality (applyVarMap varMap t1) (applyVarMap varMap t2) info)
            )
            
   explicit =
      do tp <- pType
         P.reservedOp lexer "::"
         ts <- pTypeScheme               
         return $ \info -> 
            ( allConstants tp ++ allConstants ts
            , \varMap -> ConInst (ExplicitInstance (applyVarMap varMap tp) (applyVarMap varMap ts) (const info,const id))
            )     

   implicit =
      do t1 <- pType
         P.reservedOp lexer "<="
         (monos, t2) <- P.parens lexer $ 
                           do ms <- P.brackets lexer (commas (P.identifier lexer))
                              P.lexeme lexer (char ',')
                              tp <- pType2
                              return (map TCon ms, tp)
         return $ \info ->
            ( allConstants t1 ++ allConstants monos ++ allConstants t2
            , \varMap -> ConInst (ImplicitInstance (applyVarMap varMap t1) (applyVarMap varMap monos) (applyVarMap varMap t2) (const info, const id)) 
            )
            
   predicate =
      do p <- pPredicate
         return $ \info ->
            ( allConstants p
            , \varMap -> ConPred (PredicateConstraint (applyVarMap varMap p) info)
            )

pInfo :: CharParser () String
pInfo = do P.reservedOp lexer ":"
           s <- manyTill anyChar (do { char '\n' ; return () } <|> eof)
           P.whiteSpace lexer
           return s

pTypeScheme :: CharParser () TpScheme
pTypeScheme = do qs <- option [] $
                          do P.reserved lexer "forall"
                             xs <- many1 (P.identifier lexer)
                             P.symbol lexer "."
                             return xs
                 ps <- pPredicates
                 tp <- pType
                 let sub = zip qs (map TVar [10000..])
                 return (quantify (ftv $ map snd sub) (map (applyVarMap sub) ps .=>. applyVarMap sub tp))

pPredicates :: CharParser () Predicates
pPredicates =  try (
               do p <- pPredicate
                  P.reservedOp lexer "=>"
                  return [p])
           <|> try (
               do ps <- P.parens lexer (commas pPredicate)
                  P.reservedOp lexer "=>"
                  return ps)
           <|> return []

pPredicate :: CharParser () Predicate
pPredicate = do s  <- P.identifier lexer
                tp <- pType2
                return (Predicate s tp)
                 
pType :: CharParser () Tp
pType = do left <- pType1
           option left $
             do P.reservedOp lexer "->"
                right <- pType
                return (left .->. right)

pType1 :: CharParser () Tp
pType1 = do tps <- many1 pType2
            return (foldl1 TApp tps)
      
pType2 :: CharParser () Tp
pType2 =  do s <- P.identifier lexer
             return (TCon s)
      <|> do tps <- P.parens lexer (commas pType)
             case tps of
                [tp] -> return tp
                _    -> return (tupleType tps)
      <|> do tp <- P.brackets lexer pType
             return (listType tp)
             
commas :: CharParser () a -> CharParser () [a]
commas  p = p `sepBy` P.lexeme lexer (char ',')
