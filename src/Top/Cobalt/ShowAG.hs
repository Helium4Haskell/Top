module Top.Cobalt.ShowAG where

import Data.Char
import Top.Cobalt.AGSyntax

instance Show AGCode where 
   show (AGCode ds as ss) = 
      unlines [ unlines $ map show ds
              , unlines $ map show as
              , unlines $ map show ss
              ]

instance Show AGData where 
   show (AGData nt alt cs) = 
      let f tp | all isAlpha tp = tp
      in unlines $ 
            ("DATA " ++ nt ++ " | " ++ alt) :
            [ "   " ++ c ++ " : " ++ f tp | (c, tp) <- cs  ]

instance Show AGAttr where 
   show (AGAttr nt attr s tp) = 
      let (before, after) = 
             case attr of
                Inherited   -> (" [ ", " | | ]")
                Chained     -> (" [ | ", " | ]")
                Synthesized -> (" [ | | ", " ]")
      in "ATTR " ++ nt ++ before ++ s ++ ":{" ++ tp ++ "}" ++ after

instance Show AGSem where 
   show (AGSem nt alt decls) = 
      unlines $
         ("SEM " ++ nt ++ " | " ++ alt) :
         (map (("   "++) . show) decls)

instance Show AGSemDecl where
   show (AGSemDecl a b c) =
      a ++ "." ++ b ++ " = " ++ c

instance Show Attr where 
   show Inherited   = "Inherited"
   show Chained     = "Chained" 
   show Synthesized = "Synthesized"
