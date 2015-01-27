{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DeriveFunctor        #-}

-- | Module pertaining to Refnement Type descriptions and conversions
--   Likely mergeable with @Language.Nano.Typecheck.Types@

module Language.Nano.Liquid.Types ( 
  
  -- * Refinement Types and Environments
    RReft
  , RefType 
  , RefHeap
  , REnv
  , NanoRefType
  , Loc

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
  , mkProp
  , pSingleton
  , isNil
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
  , efoldRType
  , expandTApp
  
  -- * RefHeaps
  , heapReadType
  , heapReadSym
  , mapLocTy
  , mapLocTyM
  , refHeap
  , refHeapFromBinds
  , refHeapFromTyBinds
  , refHeapMakeConc
  , isConc
  , locTy
  , locSym
  , refHeapBinds
  
  , AnnTypeR
  ) where

import           Data.Monoid 
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
import           Language.Fixpoint.Names (propConName)
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
type RefHeap     = Heap (Loc RReft)
type NanoRefType = Nano (AnnType_ RReft) RefType 

type AnnTypeR    = AnnType_ RReft
  
data Loc r       = LocB (Bind r) 
                 | LocX F.Symbol
                    deriving (Ord, Eq, Show, Functor)
                             
locTy m _ (LocB (B _ t)) = t
locTy m g (LocX x)       = maybe err id $ envFindTy x (renv g)
  where err = error ("locTy: " ++ m ++ ">" ++ ppshow x)
              
locSym (LocB (B x _)) = x
locSym (LocX x)       = x
                        
mapLocTy f (LocB (B x t)) = LocB . B x $ f t
mapLocTy _ l              = l

mapLocTyM m (LocB (B x t)) = LocB <$> m (B x t)
mapLocTyM _ l              = return l
                             
instance F.Symbolic (Loc r) where
  symbol (LocB (B x _)) = x
  symbol (LocX s)       = s
                          
refHeapBinds :: RefHeap -> [F.Symbol]
refHeapBinds h = F.symbol <$> heapTypes h

instance (F.Reftable a) => PP (Loc a) where
  pp (LocB b) = pp b
  pp (LocX t) = pp t
                
instance (F.Reftable a, F.Subable a) => F.Subable (Loc a) where
  syms (LocB (B _ t)) = F.syms t
  syms (LocX a)       = []
  subst s             = fmap (F.subst s)
  substf f            = fmap (F.substf f)
  substa f            = fmap (F.substa f)
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
  -- pp (CGE {-_ -} re rh _ gs) = vcat [pp re, pp rh, pp gs] 
  pp (CGE {-_ -} re rh _ gs) = pp rh

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
  rType = ofType . toType            -- removes all refinements

mkProp = F.PBexp . F.EApp (F.Loc F.dummyPos $ F.symbol propConName) . (: [])

eSingleton      :: (F.Expression e) => RefType -> e -> RefType 
eSingleton t e  = t `strengthen` (ureft $ F.exprReft e)

pSingleton      :: (F.Predicate p) => RefType -> p -> RefType 
pSingleton t p  = t `strengthen` (ureft $ F.propReft p)

------------------------------------------------------------------------------------------
mapReftM :: (F.Reftable b, Monad m, Applicative m) => (a -> m b) -> (a -> m b) -> RType a -> m (RType b)
------------------------------------------------------------------------------------------
mapReftM f g (TVar α r)          = TVar α <$> f r
mapReftM f g (TApp c ts rs r)    = TApp c <$> mapM (mapReftM f g) ts <*> mapM (mapRefM f g) rs <*> f r
mapReftM f g (TFun xts t h h' _) = TFun   <$> mapM (mapReftBindM f g) xts
                                        <*> mapReftBindM f g t
                                        <*> mapReftHeapM f g h
                                        <*> mapReftHeapM f g h'
                                        <*> (return mempty)
mapReftM f g (TAll α t)          = TAll α <$> mapReftM f g t
mapReftM f g (TAllP π t)         = TAllP π <$> mapReftM f g t
mapReftM f g (TObj bs r)         = TObj   <$> mapM (mapReftBindM f g) bs <*> f r
mapReftM _ _ _                   = error "Not supported in mapReftM"

mapReftBindM f g (B x t)         = B x <$> mapReftM f g t

mapRefM f g (PMono xs r)         = PMono xs <$> g r
mapRefM f g (PPoly xs t)         = PPoly xs <$> mapReftM f g t

mapReftHeapM :: (F.Reftable b, Monad m, Applicative m) => (a -> m b) -> (a -> m b) -> RHeapEnv a -> m (RHeapEnv b)
mapReftHeapM f g h             =
    mapM mapBindM (heapBinds h) >>= (return . heapFromBinds "mapReftHeapM")
        where mapBindM (l, t) = do t' <- (mapReftBindM f g) t
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
    f (U (F.Reft (_,ras)) (Pr ps)) = null ras -- && null ps

------------------------------------------------------------------------------------------
prefixOpRTy :: PrefixOp -> CGEnv -> RefType
------------------------------------------------------------------------------------------
prefixOpRTy o g = prefixOpTy o $ renv g

------------------------------------------------------------------------------------------
infixOpRTy :: InfixOp -> CGEnv -> RefType
------------------------------------------------------------------------------------------
infixOpRTy o g = infixOpTy o $ renv g

expandTApp :: REnv -> RefType -> RefType            
expandTApp γ (TApp c@(TDef _) ts rs r)
  = TApp c ts (apply θ $ appRefts ps rs) r
  where
    ps  = typeRefArgs γ c
    θ = fromLists (safeZip "appTVarArgs" (typeVarArgs γ c) (map (F.top <$>) ts)) [] :: RSubst RReft

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

heapReadType :: CGEnv -> String -> Location -> RefHeap -> RefType
heapReadType g m = heapReadWith (locTy m g) m

heapReadSym :: String -> Location -> RefHeap -> F.Symbol
heapReadSym    = heapReadWith locSym

heapReadWith f msg l σ = f $ heapRead msg l σ

refHeap :: RHeapEnv r -> Heap (Loc r)
refHeap σ = LocB <$> σ
            
refHeapFromBinds :: F.Symbolic s => String -> [(Location, s)] -> RefHeap
refHeapFromBinds msg bs = heapFromBinds msg $ map toLoc bs
  where                                                   
    toLoc = fmap (LocX . F.symbol)

refHeapFromTyBinds :: String -> [(Location, Bind RReft)] -> RefHeap
refHeapFromTyBinds msg bs = heapFromBinds msg $ map toLoc bs
  where                                                   
    toLoc = fmap LocB 

refHeapMakeConc :: String -> Location -> RefHeap -> (F.Symbol, RefType, RefHeap)
refHeapMakeConc m l σ = 
  case heapRead m l σ of
    LocX _ -> error ("Already concrete: " ++ l ++ ": " ++ m)
    LocB (B x t) -> (x, t, heapUpd l (LocX x) σ)

isConc :: String -> Location -> RefHeap -> Bool
isConc m l σ =
  case heapRead m l σ of
    LocX _ -> True
    _      -> False

efoldExt g xt γ             = F.insertSEnv (b_sym xt) (g $ b_type xt) γ

efoldRType :: (F.Reftable r) => (RType r -> b) -> (F.SEnv b -> RType r -> a -> a) -> F.SEnv b -> a -> RType r -> a
efoldRType g f = go
  where
    go γ z t@(TVar _ _) = f γ t z
    go γ z t@(TApp _ ts _ r) = f γ t $ gos (efoldExt g (B (rTypeValueVar t) t) γ) z ts
    go γ z t@(TAll _ t1) = f γ t $ go γ z t1
    go γ z t@(TAllP _ t1) = f γ t $ go γ z t1
    go γ z t@(TFun xts rt h h' r) = f γ t $ gos γ' z ts
      where 
        γ' = foldr (efoldExt g) γ (rt:xts ++ heapTypes h ++ heapTypes h')
        ts = (b_type <$> (rt:xts)) ++ heapTypes (b_type <$> h) ++ heapTypes (b_type <$> h')
    go γ z t@(TObj xts r) = f γ t $ gos γ' z (b_type <$> xts)
      where
        γ' = foldr (efoldExt g) γ xts
    gos γ z ts                = L.foldl' (go γ) z ts

isNil x =
  mkProp $ F.EApp (F.Loc F.dummyPos $ F.symbol "nil") [F.eVar x] :: F.Pred
