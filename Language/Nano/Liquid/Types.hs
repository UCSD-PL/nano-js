{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

-- | Module pertaining to Refinement Type descriptions and conversions
--   Likely mergeable with @Language.Nano.Typecheck.Types@

module Language.Nano.Liquid.Types ( 
  
  -- * Refinement Types and Environments
    RReft
  , RefType 
  , RefHeap
  , REnv
  , NanoRefType

  -- * Constraint Environments
  , CGEnv (..)
  , emptyCGEnv

  -- * Constraint Information
  , Cinfo (..)
  , ci

  -- * Constraints
  , SubC (..) , WfC (..)
  , FixSubC   , FixWfC

  -- * Conversions
  , RefTypable (..)
  , eSingleton
  , pSingleton
  -- , shiftVVs

  -- * Predicates On RefType 
  , isBaseRType
  , isTrivialRefType

  -- * Monadic map (TODO: Applicative/Traversable)
  , mapReftM

  -- * Primitive Types
  , prefixOpRTy
  , infixOpRTy 

  -- * Useful Operations
  , foldReft
  , expandTApp

  -- * RefHeaps
  , safeRefReadHeap
  
  , AnnTypeR
  ) where

import           Data.Maybe             (fromMaybe) -- (catMaybes, , isJust)
import qualified Data.List               as L
import qualified Data.HashMap.Strict     as M
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser        (SourceSpan (..))

import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Env
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Subst
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Misc
import           Text.PrettyPrint.HughesPJ
import           Control.Applicative 
  
-------------------------------------------------------------------------------------
----- | Refinement Types and Environments -------------------------------------------
-------------------------------------------------------------------------------------

type RReft       = UReft F.Reft
type RefType     = RType RReft
type REnv        = Env RefType
type RefHeap     = Heap (Id SourceSpan)
type NanoRefType = Nano (AnnType_ RReft) RefType 

type AnnTypeR    = AnnType_ RReft

-------------------------------------------------------------------------------------
-- | Constraint Generation Environment  ---------------------------------------------
-------------------------------------------------------------------------------------

data CGEnv
  = CGE { 
        -- TODO: add opts 
        --opts   :: OptionConf
          renv   :: !(Env RefType) -- ^ bindings in scope 
        , rheap  :: !RefHeap       
        , fenv   :: F.IBindEnv     -- ^ fixpoint bindings
        , guards :: ![F.Pred]      -- ^ branch target conditions  
        }

emptyCGEnv = CGE {-[] -} envEmpty heapEmpty F.emptyIBindEnv []

instance PP CGEnv where
  pp (CGE {-_ -} re rh _ gs) = vcat [pp re, pp rh, pp gs] 

----------------------------------------------------------------------------
-- | Constraint Information ------------------------------------------------
----------------------------------------------------------------------------

newtype Cinfo = Ci SourceSpan deriving (Eq, Ord, Show) 

-- emptyCinfo    = Ci $ initialPos ""

ci :: (IsLocated a) => a -> Cinfo
ci = Ci . srcPos 

instance PP Cinfo where
  pp (Ci l)   = text "CInfo:" <+> pp l 

instance IsLocated Cinfo where
  srcPos (Ci x) = x

instance F.Fixpoint Cinfo where 
  toFix = pp

----------------------------------------------------------------------------
-- | Constraints -----------------------------------------------------------
----------------------------------------------------------------------------

-- | Subtyping Constraints

data SubC     
  = Sub { senv  :: !CGEnv      -- ^ Environment
        , sinfo :: !Cinfo      -- ^ Source Information
        , slhs  :: !RefType    -- ^ Subtyping LHS
        , srhs  :: !RefType    -- ^ Subtyping RHS   ... senv |- slhs <: srhs
        }

-- | Wellformedness Constraints

data WfC 
  = W { wenv  :: !CGEnv      -- ^ Scope/Environment
      , winfo :: !Cinfo      -- ^ Source Information
      , wtyp  :: !RefType    -- ^ Type to be Well-formed ... wenv |- wtyp
      }

instance PP F.Reft where 
  pp = pprint

instance PP SubC where
  pp (Sub γ i t t') = pp (renv γ) $+$ pp (guards γ) 
                        $+$ ((text "|-") <+> (pp t $+$ text "<:" $+$ pp t'))
                        $+$ ((text "from:") <+> pp i) 

instance PP WfC where
  pp (W γ t i)      = pp (renv γ) 
                        $+$ (text "|-" <+> pp t) 
                        $+$ ((text "from:") <+> pp i) 

instance IsLocated SubC where
  srcPos = srcPos . sinfo

instance IsLocated WfC where
  srcPos = srcPos . winfo

-- | Aliases for Fixpoint Constraints

type FixSubC = F.SubC Cinfo
type FixWfC  = F.WfC  Cinfo

------------------------------------------------------------------------
-- | Embedding Values as RefTypes --------------------------------------
------------------------------------------------------------------------

class RefTypable a where
  rType :: a -> RefType 

instance RefTypable Type where
  rType = ofType

instance RefTypable RefType where
  rType = ofType . toType           -- removes all refinements

eSingleton      :: (F.Expression e) => RefType -> e -> RefType 
eSingleton t e  = t `strengthen` (ureft $ F.exprReft e)

pSingleton      :: (F.Predicate p) => RefType -> p -> RefType 
pSingleton t p  = t `strengthen` (ureft $ F.propReft p)

------------------------------------------------------------------------------------------
mapReftM :: (F.Reftable b, Monad m, Applicative m) => (a -> m b) -> RType a -> m (RType b)
------------------------------------------------------------------------------------------
mapReftM f (TVar α r)          = TVar α <$> f r
mapReftM f (TApp c ts rs r)    = TApp c <$> mapM (mapReftM f) ts <*> mapM (mapRefM f) rs <*> f r
mapReftM f (TFun xts t h h' _) = TFun   <$> mapM (mapReftBindM f) xts
                                        <*> mapReftBindM f t
                                        <*> mapReftHeapM f h
                                        <*> mapReftHeapM f h'
                                        <*> (return F.top) --f r 
mapReftM f (TAll α t)          = TAll α <$> mapReftM f t
mapReftM f (TAllP π t)         = TAllP π <$> mapReftM f t
mapReftM f (TObj bs r)         = TObj   <$> mapM (mapReftBindM f) bs <*> f r
mapReftM _ _                   = error "Not supported in mapReftM"

mapReftBindM f (B x t)         = B x <$> mapReftM f t

mapRefM f (PMono xs r)         = PMono xs <$> f r
mapRefM f (PPoly xs t)         = PPoly xs <$> mapReftM f t

mapReftHeapM :: (F.Reftable b, Monad m, Applicative m) => (a -> m b) -> RHeapEnv a -> m (RHeapEnv b)
mapReftHeapM f h               =
    mapM mapBindM (heapBinds h) >>= (return . heapFromBinds "mapReftHeapM")
        where mapBindM (l, t) = do t' <- (mapReftBindM f) t
                                   return (l, t')

------------------------------------------------------------------------------------------
isBaseRType :: RType r -> Bool
------------------------------------------------------------------------------------------
isBaseRType (TApp _ [] _ _) = True
isBaseRType (TVar _ _)      = True
isBaseRType _               = False

------------------------------------------------------------------------------------------
isTrivialRefType :: RefType -> Bool
------------------------------------------------------------------------------------------
isTrivialRefType t     = foldReft (\r -> (f r &&)) True t
  where 
    f (U (F.Reft (_,ras)) (Pr ps)) = null ras && null ps

------------------------------------------------------------------------------------------
prefixOpRTy :: PrefixOp -> CGEnv -> RefType
------------------------------------------------------------------------------------------
prefixOpRTy o g = prefixOpTy o $ renv g

------------------------------------------------------------------------------------------
infixOpRTy :: InfixOp -> CGEnv -> RefType
------------------------------------------------------------------------------------------
infixOpRTy o g = infixOpTy o $ renv g

safeRefReadHeap :: String -> CGEnv -> RefHeap -> Location -> (Id SourceSpan, RefType)
safeRefReadHeap m g σ l = (x, t)
  where x = heapRead m l σ
        t = maybe (error m) id (envFindTy x $ renv g)

expandTApp :: REnv -> RefType -> RefType            
expandTApp γ (TApp c@(TDef _) ts rs r)
  = TApp c ts (tracePP "expandTApp" $ apply θ $ appRefts ps rs) r
  where
    ps  = typeRefArgs γ c
    θ = fromLists (safeZip "appTVarArgs" (typeVarArgs γ c) (map (const F.top <$>) ts)) [] :: RSubst RReft

expandTApp _ t
  = t

appRefts ps [] = PPoly [] . ofType . pv_ty <$> ps
appRefts ps rs = safeZipWith "appRefts" toPoly rs ps

toPoly (PPoly ss t) p
  | length (pv_as p) == length ss
  = PPoly ss t
  | otherwise
  = PPoly ([(s, t) | (t, s, _) <- pv_as p]) t
toPoly (PMono ss r) t
  = PPoly ss $ (ofType $ pv_ty t) `strengthen` r
    
