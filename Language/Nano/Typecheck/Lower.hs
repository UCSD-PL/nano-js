module Language.Nano.Typecheck.Lower (lowerTransform, padTransform) where

import           Language.Nano.Typecheck.Types

import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint

import           Language.Nano.Errors

----------------------------------------------------------------------------------
lowerTransform :: (PP t) => Nano a t -> Nano a t
----------------------------------------------------------------------------------
lowerTransform p@(Nano {code = Src fs})
  = p { code = Src $ fs }

----------------------------------------------------------------------------------
lowerStmt :: Statement a -> Statement a
----------------------------------------------------------------------------------
lowerStmt (IfStmt l b s1 s2) = IfStmt l b (padStmt s1) (padStmt s2)
lowerStmt x                  = x

----------------------------------------------------------------------------------
padTransform :: (PP t) => Nano a t -> Nano a t
----------------------------------------------------------------------------------
padTransform p@(Nano {code = Src fs})
  = p { code = Src $ map padStmt fs }


----------------------------------------------------------------------------------
padStmt :: Statement a -> Statement a
----------------------------------------------------------------------------------
padStmt (FunctionStmt lf i is ss)
  = FunctionStmt lf i is (map padStmt ss)
    
padStmt (IfStmt l b s1 s2) 
  = IfStmt l b (padStmt' s1) (padStmt' s2)

padStmt (BlockStmt l ss)
  = BlockStmt l (map padStmt ss)

padStmt x = x

padStmt' (BlockStmt l ss) = BlockStmt l $ ss ++ [EmptyStmt l]
padStmt' s                = BlockStmt (getAnnotation s) [s,EmptyStmt (getAnnotation s)]
