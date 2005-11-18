{-
   The code in this file is experimental.
	 
	 Various remarks:
     * You have only multi line comments a la Haskell, no single line comments
		 * No special error messages yet.
		 * Lots of comma's and semicolon's in contrast to a line-based approach. 
       This gives a cleaner parser. Some are redundant, but they do make the punctuation more
       consistent (e.g. the semi colon after the last premise).
		 * Error messages for constraints are modelled as a parameter to constraint function.
-}

module Top.Cobalt.ParseRules where

import List
import Parsec
import qualified ParsecPrim as Prim
import qualified ParsecToken as P
import ParsecLanguage (haskellStyle, LanguageDef(..))
import Top.Cobalt.AGSyntax
import Top.Cobalt.ShowAG
import Top.Cobalt.Syntax
import System (getArgs)

---------------------------------------------------------------------
-- * Top lexer

lexer :: P.TokenParser ()
lexer = P.makeTokenParser 
           ( haskellStyle 
                { commentLine     = ""
                , reservedOpNames = [ "|", ";", ":", "|-", "," ]
                , reservedNames   = [ "DATA", "RULE", "MACRO", "JUDGEMENT" ]
                })

-- Locals for shortening notation 
symbol        = P.symbol lexer
reservedOp    = P.reservedOp lexer
parens        = P.parens lexer
reserved      = P.reserved lexer
identifier    = P.identifier lexer
stringLiteral = P.stringLiteral lexer
commaSepBy p  = sepBy p (reservedOp ",")
commaSepBy1 p = sepBy1 p (reservedOp ",")
semiSepBy p   = sepBy p (reservedOp ";")

---------------------------------------------------------------------
-- * Some extra types and helper functions

data Alternative = AGDataAlt AGDatas | JudgementAlt JudgementDecl | TypeRuleAlt TypeRule  | MacroAlt String

assembleTypeSystem :: [Alternative] -> TypeSystem
assembleTypeSystem alts = gather alts ([],[],[],[])
  where
    gather []       ts = typeSystem ts
    gather (a:alts) ts = gather alts 
                          (case a of
                           AGDataAlt agdatas          -> cons1 agdatas ts
                           TypeRuleAlt typerule       -> cons2 typerule ts
                           MacroAlt macro             -> cons3 macro ts
                           JudgementAlt judgementdecl -> cons4 judgementdecl ts)
    cons1 x (u,v,w,z) = (x++u,v,w,z)
    cons2 x (u,v,w,z) = (u,x:v,w,z)
    cons3 x (u,v,w,z) = (u,v,x:w,z)
    cons4 x (u,v,w,z) = (u,v,w,x:z)
    typeSystem (agdatas, typerules, macros, judgements) = TypeSystem (reverse agdatas) (reverse judgements) (reverse typerules)
														
---------------------------------------------------------------------
-- * Top parser and main function

{-
main :: IO ()
main = do args <- getArgs
          case args of
             [filename] -> 
                do{ content <- readFile filename
                  ; ptest pTypeSystem content
                  }
             _ -> do{ putStrLn "Incorrect number of arguments for parsetypesystem"
                    ; putStrLn "Usage: parsetypesystem <filename>"
                    }
-}

ptest :: Show a => Parser a -> String -> IO ()
ptest p input =
   case (parse p "" input) of
      Left err -> 
         do putStr "parse error at "
            print err
      Right ts -> 
         putStrLn (show ts)
         
         
run :: Parser a -> String -> Maybe a
run p input = 
  runLexed (do { P.whiteSpace lexer
               ; x <- p
               ; eof
               ; return x
               }) 
           input

runLexed :: Parser a -> String -> Maybe a
runLexed p input =
   case (parse p "" input) of
      Left err -> 
        Nothing
      Right ts -> 
         Just ts
         
-- Parsing the type system, entry point
pTypeSystem :: Parser TypeSystem
pTypeSystem = 
  do{ items <- many pTypeSystemItem
    ; return (assembleTypeSystem items)
    }
    
pTypeSystemItem = 
  do{ reserved "DATA"
    ; agdatas <- pAGDatas
    ; return (AGDataAlt agdatas)
    }
  <|>  
  do{ reserved "JUDGEMENT"
    ; judgementdecl <- pJudgementDecl
    ; return (JudgementAlt judgementdecl)
    }						
  <|>
  do{ reserved "RULE"
    ; rule <- pTypeRule
    ; return (TypeRuleAlt rule)
    }
  <|>  
  do{ reserved "MACRO"
    ; return (MacroAlt "macro")
    }						

-- AG Data structures			
pAGDatas :: Parser AGDatas
pAGDatas = 
  do{ datatype <- identifier
	  ; cases <- many pAlternative
		; return (map (makeAGData datatype) cases)
    }

makeAGData t (alt,field) = AGData t alt field
							 
pAlternative = 
  do{ reservedOp "|"
    ; alternative <- identifier
    ; fields <- commaSepBy1 pField
	  ; return (alternative, fields)
    }
								   
pField = 
  do{ id <- identifier
    ; reservedOp ":"
    ; tp <- identifier -- Maybe this ought to be some type spec.
    ; return (id,tp)
    }


-- Type rules
pTypeRule :: Parser TypeRule
pTypeRule = 
  do{ premises <- many pJudgement
    ; skipMany1 (symbol "-")
    ; name <- pRuleName
    ; consequent <- pJudgement
    ; constraints <- commaSepBy pConstraint
    ; return (TypeRule name (DeductionRule premises consequent) constraints)
    }

-- Rather arbitrary this one: either id or [id]
pRuleName :: Parser String
pRuleName =
  do{ reservedOp "["
    ; id <- identifier
    ; reservedOp "]"
    ; return id
    }
  <|>
  identifier	 

pJudgementDecl :: Parser JudgementDecl
pJudgementDecl =
  do{ inhtypes <- commaSepBy identifier
    ; reservedOp "|-"
    ; datatype <- identifier
    ; reservedOp ":"
    ; syntypes <- commaSepBy identifier
    ; reservedOp ";"
    ; return (JudgementDecl datatype inhtypes syntypes)  
    }
    
pJudgement :: Parser Judgement
pJudgement =
  do{ inhs <- commaSepBy pTerm 
    ; reservedOp "|-"
    ; expr <- pTerm
    ; reservedOp ":"
    ; syns <- commaSepBy pTerm 
    ; reservedOp ";"
    ; return (Judgement inhs expr syns)
    }

pConstraint :: Parser ConstraintTerm
pConstraint = 
  do{ term <- pTerm
    ; return (ConstraintTerm term)
    }
 

pTerm :: Parser Term
pTerm =
  do{ hd <- identifier 
		; terms	<- many pAtom
    ; return (if (null terms) then (TermVar hd) else (TermApp hd terms))
		}
  <|>
	parens pTerm

pAtom :: Parser Term
pAtom = do{ id <- identifier 
          ; return (TermVar id)
          }
        <|>
				do{ string <- stringLiteral
				  ; return (TermString string)
					}
				<|>
        parens pTerm

-- The pretty printing section. Not clever in the use of parentheses.

ppTypeSystem :: TypeSystem -> String
ppTypeSystem (TypeSystem agdatas judgementDecls typerules)
  = ppAGDatas agdatas ++ "\n" ++
	  unlines (map ppJudgementDecl judgementDecls) ++
    if (null typerules) then "" else unlines (map ppTypeRule typerules)

ppAGDatas :: AGDatas -> String
ppAGDatas = concatMap show

ppJudgementDecl :: JudgementDecl -> String
ppJudgementDecl (JudgementDecl datatype inhtypes syntypes ) =
  "JUDGEMENT " ++ 
  ppWithSep ", " inhtypes 
  ++ "|- " ++
  datatype
  ++ " : " ++
  ppWithSep ", " syntypes
  ++ "\n"
  
ppTypeRule :: TypeRule -> String
ppTypeRule (TypeRule name deductionrule constraints) = 
  "RULE\n"
  ++
  ppDeductionRule name deductionrule
	++
	"\n\n"
	++
	ppWithSep ",\n" (map ppConstraint constraints)
  ++
  "\n"

indent :: String -> String
indent xs = "   "++xs

ppDeductionRule :: String -> DeductionRule -> String
ppDeductionRule name (DeductionRule premises conclusion) =
    premisespp ++ "\n" ++ "---------------------------- " ++ name ++ "\n" ++ ppJudgement conclusion
  where
    premisespp = if (null premises) then "" else ppWithSep "\n" (map ppJudgement premises)
    
ppJudgement :: Judgement -> String
ppJudgement (Judgement inhs expr syns) = 
  indent (ppWithSep ", " (map ppStrippedTerm inhs)
        	++ 
         	" |- " ++ ppStrippedTerm expr ++ " : " 
        	++ 
        	ppWithSep ", " (map ppStrippedTerm syns)
          ++ ";")

ppConstraint :: ConstraintTerm -> String
ppConstraint (ConstraintTerm term) =  ppStrippedTerm term

ppStrippedTerm :: Term -> String
ppStrippedTerm = ppStripOuterParens . ppTerm

ppTerm :: Term -> String
ppTerm (TermVar v) = v
ppTerm (TermString m) = show m
ppTerm (TermApp f args) = "(" ++ f ++ " " ++ unwords (map ppTerm args) ++ ")"

instance Show TypeSystem where show = ppTypeSystem
instance Show TypeRule where show = ppTypeRule
instance Show DeductionRule where show = ppDeductionRule "dummyname"
instance Show Judgement where show = ppJudgement
instance Show ConstraintTerm where show = ppConstraint
instance Show Term where show = ppTerm

ppWithSep :: String -> [String] -> String
ppWithSep sep xs = concat (intersperse sep xs)

ppStripOuterParens xs = if (head xs == '(') && (last xs == ')') then tail (init xs) else xs

testparser = do { content <- readFile "HM.type" ; ptest pTypeSystem content }
