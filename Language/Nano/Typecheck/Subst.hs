{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE OverlappingInstances #-}

module Language.Nano.Typecheck.Subst ( 
  
  -- * Substitutions
    RSubst (..)
  , Subst 
  , toList
  , fromList

  -- * Free Type Variables
  , Free (..)

  -- * Type-class with operations
  , Substitutable (..)

  -- * Unfolding
  , unfoldFirst, unfoldMaybe, unfoldSafe
  

  ) where 

import           Text.PrettyPrint.HughesPJ
import           Language.ECMAScript3.PrettyPrint
import qualified Language.Fixpoint.Types as F
import           Language.Nano.Errors 
import           Language.Nano.Env
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps

import           Control.Applicative ((<$>))
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M 
import           Data.Monoid
import           Text.Printf 
-- import           Debug.Trace
-- import           Language.Nano.Misc (mkEither)

---------------------------------------------------------------------------
-- | Substitutions --------------------------------------------------------
---------------------------------------------------------------------------

-- | Type alias for Map from @TVar@ to @Type@. Hidden

data RSubst r = Su { tySub  :: M.HashMap TVar (RType r)
                   , locSub :: M.HashMap Location Location
                   }

type Subst    = RSubst ()

-- TODO fix and rename
toList        :: RSubst r -> [(TVar, RType r)]
toList (Su m _) =  M.toList m 

fromList      :: [(TVar, RType r)] -> RSubst r
fromList      = flip Su M.empty . M.fromList 

-- | Substitutions form a monoid; not commutative

instance (F.Reftable r, Substitutable r (RType r)) => Monoid (RSubst r) where 
  mempty                             = Su M.empty M.empty
  mappend (Su m1 m2) θ'@(Su m1' m2') =
      Su ((apply θ' <$> m1) `M.union` m1')
         ((apply θ' <$> m2) `M.union` m2')

instance (F.Reftable r, PP r) => PP (RSubst r) where 
  pp (Su m1 m2) = if M.null m1 && M.null m2 then
                      text "empty"
                  else
                      (vcat $ (ppBind <$>) $ M.toList m1)
                      <+> (vcat $ (ppBind <$>) $ M.toList m2)

ppBind (x, t) = pp x <+> text ":=" <+> pp t

---------------------------------------------------------------------------
-- | Substitutions --------------------------------------------------------
---------------------------------------------------------------------------

class Free a where 
  free  :: a -> S.HashSet TVar

class Substitutable r a where 
  apply :: (RSubst r) -> a -> a 

instance Free a => Free [a] where 
  free = S.unions . map free

instance Substitutable r a => Substitutable r [a] where 
  apply = map . apply 

instance Substitutable r Location where
  apply (Su _ lsub) l = M.lookupDefault l l lsub

--TODO fix, this is just wrong
instance (PP r, F.Reftable r, Substitutable r (RType r)) =>
    Substitutable r (Heap (RType r)) where
  apply θ h =
      heapFromBinds $ map (apply θ) $ heapBinds h

instance (Substitutable r a, Substitutable r b) => Substitutable r (a,b) where 
  apply f (x,y) = (apply f x, apply f y)

instance (PP r, F.Reftable r) => Substitutable r (RType r) where 
  apply θ t = appTy θ t
--     where 
--       msg   = printf "apply [θ = %s] [t = %s]" (ppshow θ) (ppshow t)

instance (PP r, F.Reftable r) => Substitutable r (Bind r) where 
  apply θ (B z t) = B z $ appTy θ t

instance Free (RType r) where
  free (TApp _ ts _)        = S.unions   $ free <$> ts
  free (TVar α _)           = S.singleton α 
  free (TFun xts t h h' _)  = S.unions   $ free <$> t:ts where ts = (b_type <$> xts) ++ heapTypes h ++ heapTypes h'
  free (TAll α t)           = S.delete α $ free t 
  free (TObj bs _)          = S.unions   $ free <$> b_type <$> bs
  free (TBd (TD _ α t _ ))  = foldr S.delete (free t) α

instance Substitutable () Fact where
  apply _ x@(PhiVar _)  = x
  apply θ (TypInst ts)  = TypInst $ apply θ ts
  apply θ (Assume  t )  = Assume  $ apply θ t

instance Free Fact where
  free (PhiVar _)       = S.empty
  free (TypInst ts)     = free ts
  free (Assume t)       = free t
 
------------------------------------------------------------------------
-- appTy :: RSubst r -> RType r -> RType r
------------------------------------------------------------------------
appTy (Su _ m) (TApp (TRef l) t z)  = TApp (TRef $ M.lookupDefault l l m) t z
appTy θ (TApp c ts z)               = TApp c (apply θ ts) z 
appTy θ (TObj bs z)                 = TObj (map (\b -> B { b_sym = b_sym b, b_type = appTy θ $ b_type b } ) bs ) z
appTy (Su m _) t@(TVar α r)         = (M.lookupDefault t α m) `strengthen` r
appTy θ (TFun ts t h h' r)          = appTyFun θ ts t h h' r
appTy (Su ts ls) (TAll α t)         = apply (Su (M.delete α ts) ls) t 
appTy (Su ts ls) (TBd (TD c α t s)) = TBd $ TD c α (apply (Su (foldr M.delete ts α) ls) t) s

appTyFun θ ts t h h' r =
  TFun (apply θ ts) (apply θ t) (fmap go h) (fmap go h') r
      where go = appTy θ

-- | Unfold the FIRST TDef at any part of the type @t@.
-------------------------------------------------------------------------------
unfoldFirst :: (PP r, F.Reftable r) => Env (RType r) -> RType r -> RType r
-------------------------------------------------------------------------------
unfoldFirst env t = go t
  where 
    go (TFun its ot h h' r)         = TFun (appTBi go <$> its) (go ot) (fmap go h) (fmap go h') r
    go (TObj bs r)             = TObj (appTBi go <$> bs) r
    go (TBd  _)                = error "unfoldTDefDeep: there should not be a TBody here"
    go (TAll v t)              = TAll v $ go t
    go (TApp (TDef id) acts _) = 
      case envFindTy (F.symbol id) env of
        Just (TBd (TD _ vs bd _ )) -> apply (fromList $ zip vs acts) bd
        _                          -> error $ errorUnboundId id
    go (TApp c a r)            = TApp c (go <$> a) r
    go t@(TVar _ _ )           = t
    appTBi f (B s t)           = B s $ f t


-- | Unfold a top-level type definition once. 
-- Return @Right t@, where @t@ is the unfolded type if the unfolding is succesful.
-- This includes the case where the input type @t@ is not a type definition in
-- which case the same type is returned.
-- If it is a type literal for which no definition exists return 
-- @Left "<Error message>".
--
-- TODO: Make sure toplevel refinements are the same.
-------------------------------------------------------------------------------
unfoldMaybe :: (PP r, F.Reftable r) => Env (RType r) -> RType r -> Either String (RType r)
-------------------------------------------------------------------------------
unfoldMaybe env t@(TApp (TDef id) acts _) =
      case envFindTy (F.symbol id) env of
        Just (TBd (TD _ vs bd _ )) -> Right $ apply (fromList $ zip vs acts) bd
        _                          -> Left  $ (printf "Failed unfolding: %s" $ ppshow t)
-- The only thing that is unfoldable is a TDef.
-- The rest are just returned as they are.
unfoldMaybe _ t                           = Right t


-- | Force a successful unfolding
-------------------------------------------------------------------------------
unfoldSafe :: (PP r, F.Reftable r) => Env (RType r) -> RType r -> RType r
-------------------------------------------------------------------------------
unfoldSafe env = either error id . unfoldMaybe env

