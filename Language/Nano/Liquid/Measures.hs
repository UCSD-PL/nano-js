{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}

module Language.Nano.Liquid.Measures  where

import           Language.ECMAScript3.PrettyPrint

import           Language.Fixpoint.Types            
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Misc

import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Parse
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Unify
import           Language.Nano.Liquid.Types
import           Language.Nano.Env
import           Language.Nano.Misc

import           Text.Printf                        (printf)
import           Text.PrettyPrint.HughesPJ
import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import           Control.Applicative                ((<$>))

--------------------------------------------------------------------------------
instMeasures :: Symbolic s => [s] -> [Measure] -> RReft
--------------------------------------------------------------------------------
instMeasures args ms = foldl joinRefts (ureft $ predReft PTrue) ms
    where
      joinRefts r m = r `meet` instMeasure args m

--------------------------------------------------------------------------------
instMeasure :: Symbolic s => [s] -> Measure -> RReft
--------------------------------------------------------------------------------
instMeasure args (foo, fargs, expr) = ureft . predReft $ PAtom Eq lhs rhs
  where
    eargs = eVar <$> args
    su    = mkSubst $ zip fargs eargs
    lhs   = EApp foo eargs
    rhs   = subst su expr
            
--------------------------------------------------------------------------------
addMeasures :: REnv -> REnv -> [Measure] -> RHeapEnv RReft -> Bind RReft
            -> Bind RReft
--------------------------------------------------------------------------------
addMeasures γm γt mdefs σ t = foldl (addMeasure γm γt σ) t mdefs

--------------------------------------------------------------------------------
addMeasure :: REnv -> REnv -> RHeapEnv RReft -> Bind RReft -> Measure -> Bind RReft
--------------------------------------------------------------------------------
addMeasure γm γt σ b@(B x t) m@(_,[a],_)
    = maybe b (B x . strengthen t)
      $ addMeasure' γm γt [B (vv Nothing) t] m

addMeasure γm γt σ b@(B x t) m@(_,[a1,a2],_)
    | length ls == 1 && l `elem` heapLocs σ = try hb m
    | toType t == tNull                     = try nil m
    | otherwise                             = b
      where
        ls    = if isFalseR t then [] else refLocs t
        l     = head ls
        hb    = heapRead "addMeasure" l σ
        bv    = B (vv Nothing) t
        app p = B x (t `strengthen` p)
        try h = maybe b app . addMeasure' γm γt [bv,h]
        nil   = nilBind :: Bind RReft

addMeasure γm γt σ t _ = t

refLocs (TApp TUn ts _ _)     = concatMap refLocs ts
refLocs (TApp (TRef l) _ _ _) = [l]                         
refLocs _                     = []                         

addMeasure' γm γt ts m@(foo, fargs, expr)
    | tcMeasure γt (b_type <$> ts) (envFindTy foo γm) = Just p
    | otherwise                                       = Nothing
    where
      argTy = envFindTy foo γm
      t     = head ts
      p     = instMeasure (b_sym <$> ts) m 

tcMeasure γt ts Nothing              
    = error "BUG: addMeasure"

tcMeasure γt ts (Just f)
    = maybe False (tcMeasure' γt ts) $ bkFun f

tcMeasure' γt ts (αs,_,bs,h,_,_) 
    | length ts /= length bs =
        False
    | otherwise =
        case unifys γt θ0 ts ts' of
          Left  _ -> False
          Right θ -> and $ zipWith (st γt) ts (apply θ ts')
    where
      st γt t1 t2 | isUndefined t1 = True
                  | otherwise      = isSubType γt t1 t2
      msg t1 t2 = printf "tcMeasure' %s <: %s" (ppshow t1) (ppshow t2)
      ts' = b_type <$> bs
      αts = zip αs $ map tVar αs
      ls  = L.nub (heapLocs h ++ concatMap locs ts')
      θ0  = fromLists αts (zip ls ls)

isFalseR (TBd _     ) = False
isFalseR (TAll _ _  ) = False
isFalseR t            = isFalse . ur_reft . rTypeR $ t
