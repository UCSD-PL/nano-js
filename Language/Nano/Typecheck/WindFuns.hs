module Language.Nano.Typecheck.WindFuns (
  
    generateWindFuns
  , windFunName
  , unwindFunName
  , windLoc 

  ) where

import           Data.Maybe
import           Text.Printf

import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser    (SourceSpan (..))

import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc

import           Language.Nano.CmdLine              (getOpts)
import           Language.Nano.Env
import           Language.Nano.Errors
import           Language.Nano.Types
import qualified Language.Nano.Annots               as A

import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Parse
import           Language.Nano.Typecheck.Subst

--------------------------------------------------------------------------
windLoc :: Location
--------------------------------------------------------------------------
windLoc = "X"

--------------------------------------------------------------------------
windFunName :: Id l -> Id l
--------------------------------------------------------------------------
windFunName (Id l s) = Id l ("wind_" ++ s)

--------------------------------------------------------------------------
unwindFunName :: Id l -> Id l
--------------------------------------------------------------------------
unwindFunName (Id l s) = Id l ("unwind_" ++ s)

--------------------------------------------------------------------------
generateWindFuns :: (PP r, F.Reftable r) => Env (RType r) -> Env (RType r) 
--------------------------------------------------------------------------
generateWindFuns e
  = envFromList . concat . catMaybes . map (generateWindPair) $ envToList e

generateWindPair :: (PP r, F.Reftable r) => (Id SourceSpan, RType r) -> Maybe [(Id SourceSpan, RType r)]
generateWindPair (i,t@(TBd b))
  = Just [generateWindFn b, generateUnWindFn b]
  where 
    windFnBnd = generateWindFn b

generateWindPair _ = Nothing

generateWindFn (TD d@(TDef i) αs σ bd l)
  = (windFunName i, windFnTemplate d αs σi σo)
  where 
    σi = locPreWindHeap bd σ
    σo = locWindHeap $ woundType d αs

generateUnWindFn (TD d@(TDef i) αs σ bd l)
  = (unwindFunName i, windFnTemplate d αs σi σo)
  where 
    σi = locWindHeap $ woundType d αs
    σo = locPreWindHeap bd σ
          
windFnTemplate n αs σ σ'          
  = foldAlls αs fn
  -- where fn = TFun [B (F.symbol "$$loc") tString] tVoid σ σ' F.top
  where fn = TFun [] tVoid σ σ' F.top

woundType d αs = TApp d (fmap tVar αs) F.top
                                   
locArg  = B (F.symbol windLoc) (tRef windLoc)
locHeap t   = heapAdd "locHeap" windLoc t $ heapEmpty
locPreWindHeap t σ = heapCombine "locPreWindHeap" [locHeap t, σ]
locWindHeap d =locHeap d
               
foldAlls [] t = t               
foldAlls (α:αs) t = TAll α (foldAlls αs t)
