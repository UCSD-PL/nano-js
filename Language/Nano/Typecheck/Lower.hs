module Language.Nano.Typecheck.Lower (

    lowerTransform
  , padTransform
  -- , genNano

  ) where

import           Control.Monad.State

import qualified Data.HashSet                       as HS 
import qualified Data.HashMap.Strict                as M 

import           Language.Nano.Typecheck.Types
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser        (SourceSpan (..))
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
  = IfStmt l b (padIfStmts s1) (padIfStmts s2)

padStmt (BlockStmt l ss)
  = BlockStmt l (map padStmt ss)

padStmt x = x

padIfStmts s@(EmptyStmt l)  = BlockStmt l [s]
padIfStmts (BlockStmt l ss) = BlockStmt l $ (map padStmt ss) ++ [EmptyStmt l]
padIfStmts s                = BlockStmt (getAnnotation s) [padStmt s,EmptyStmt (getAnnotation s)]
{- 
type GenSet f = M.HashMap (SourceSpan) (Id (Annot f SourceSpan))
type OutSet f = M.HashMap (SourceSpan) (Id (Annot f SourceSpan))

lvaNano :: (PP t) => Nano (Annot f SourceSpan) t -> Nano (Annot f SourceSpan) t
lvaNano p@(Nano {code = Src fs})
  = let inSets = genNano p
        
    in error "foo" 

lvaFun inSets s@(FunctionStmt l f xs body) 
  = foldl (\(b,inSets) -> b || lvaStmt inSets) (False,inSets) body

lvaStmts inSets (s1:s2:ss)
  = inSets s1 
-------------------------------------------------------------------------------------
lvaStmt :: OutSet f -> Statement (Annot f SourceSpan) -> (Boolean, GenSet f)
-------------------------------------------------------------------------------------
lvaStmt inSets s@(VarDeclStmt l ds)
  = foldl (\(b,inSets) (VarDecl _ i _) -> M.insert (ann l) i m) M.empty ds

lvaStmt inSets
  = (False, inSets)

-- s1;s2;...;sn
genStmt (BlockStmt l stmts) 
  = foldl (\m s -> m `M.union` genStmt s) M.empty stmts

-- if b { s1 }
genStmt (IfSingleStmt l b s)
  = genStmt (IfStmt l b s (EmptyStmt l))

-- if b { s1 } else { s2 }
genStmt (IfStmt l e s1 s2)
  = genStmt s1 `M.union` genStmt s2

-- var x1 [ = e1 ]; ... ; var xn [= en];
genStmt s@(VarDeclStmt l ds)
  = foldl (\m (VarDecl _ i _) -> M.insert (ann l) i m) M.empty ds

-- function f(...){ s }
genStmt s@(FunctionStmt _ _ _ _)
  = genFun s

-- OTHER (Not handled)
genStmt s 
  = M.empty

genNano :: (PP t) => Nano (Annot f SourceSpan) t -> Nano (Annot f SourceSpan) t
genNano p@(Nano {code = Src fs})
  = M.toList $ foldl (\m s -> m `M.union` genStmt s) M.empty fs

genFun s@(FunctionStmt l f xs body) 
  = foldl (\m s -> m `M.union` genStmt s) M.empty body

-------------------------------------------------------------------------------------
genStmt :: Statement (Annot f SourceSpan) -> GenSet f
-------------------------------------------------------------------------------------
-- s1;s2;...;sn
genStmt (BlockStmt l stmts) 
  = foldl (\m s -> m `M.union` genStmt s) M.empty stmts

-- if b { s1 }
genStmt (IfSingleStmt l b s)
  = genStmt (IfStmt l b s (EmptyStmt l))

-- if b { s1 } else { s2 }
genStmt (IfStmt l e s1 s2)
  = genStmt s1 `M.union` genStmt s2

-- var x1 [ = e1 ]; ... ; var xn [= en];
genStmt s@(VarDeclStmt l ds)
  = foldl (\m (VarDecl _ i _) -> M.insert (ann l) i m) M.empty ds

-- function f(...){ s }
genStmt s@(FunctionStmt _ _ _ _)
  = genFun s

-- OTHER (Not handled)
genStmt s 
  = M.empty
   -}
