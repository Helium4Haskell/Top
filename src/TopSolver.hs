module Main where

import Parsec
import qualified ParsecToken as P
import ParsecLanguage (haskellStyle)
import Top.Types
import Top.Constraints.EqualityConstraint
import Top.Solvers.SolveConstraints
import Top.TypeGraph.TypeGraphSolver
import System (getArgs)
import Char
import List

lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
           ( haskellStyle )

run :: Parser [EqualityConstraint String] -> String -> IO ()
run p input
           = case (parse p "" input) of
               Left err -> do{ putStr "parse error at "
                             ; print err
                             }
               Right cs -> 
                  let vars   = filter (isLower . head) (nub (concat [ constantsInType t1 ++ constantsInType t2 | Equality t1 t2 _ <- cs ]))
                      sub    = zip vars (map TVar [0..])
                      cs'    = let f (TApp l r) = TApp (f l) (f r)
                                   f (TCon s) = maybe (TCon s) id (lookup s sub)
                                   f tp = tp
                               in [ Equality (f t1) (f t2) info | Equality t1 t2 info <- cs]
                      result = solveTypeGraph [] noOrderedTypeSynonyms (length vars) cs'
                  in do putStrLn (debugFromResult result)
                        putStrLn (replicate 50 '-')
                        case errorsFromResult result of
                           [] -> putStrLn "(No errors)" 
                           es -> do putStr (unlines es)
                                    putStrLn ("(Failed with "++show (length es)++" errors)")
                           
                       
                      
runLex :: Parser [EqualityConstraint String] -> String -> IO ()
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

pConstraint :: CharParser () (EqualityConstraint String)
pConstraint =
   do t1 <- pType
      P.reservedOp lexer "=="
      t2 <- pType      
      P.reservedOp lexer ":"
      info <- manyTill anyChar (do { char '\n' ; return () } <|> eof)
      P.whiteSpace lexer
      return (Equality t1 t2 info)
     

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
