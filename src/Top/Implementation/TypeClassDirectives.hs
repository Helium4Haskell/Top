module Top.Implementation.TypeClassDirectives where

import Top.Types.Primitive
import Top.Types.Classes

    -- Type class directives
type TypeClassDirectives info = [TypeClassDirective info]

data TypeClassDirective info 
   = NeverDirective     Predicate  info
   | CloseDirective     String     info
   | DisjointDirective  [String]   info
   | DefaultDirective   String Tps info

instance Show (TypeClassDirective info) where
    show (NeverDirective predicate info) = show predicate
    show (CloseDirective n info) = show n
    show (DisjointDirective ns info) = show ns
    show (DefaultDirective n tps info) = show n ++ show tps