{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TupleSections #-}

module Language.Nano.Typecheck.Subst ( 
  
  -- * Substitutions
    RSubst (..)
  , Subst 
  , toLists
  , fromLists
  , toSubst

  -- * Free Type Variables
  , Free (..)

  -- * Type-class with operations
  , Substitutable (..)

  -- * Unfolding
  , unfoldFirst, unfoldMaybe, unfoldSafe
  
  -- * Accessing fields
  , ObjectAccess(..)
  , dotAccessRef

  ) where 

import           Text.PrettyPrint.HughesPJ
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.Parser    (SourceSpan (..))
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Misc
import           Language.Nano.Errors 
import           Language.Nano.Env
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps

import           Control.Applicative ((<$>))
import qualified Data.HashSet as S
import           Data.List                      (find, intersect,sort,nub)
import           Data.Traversable               (traverse)
import qualified Data.HashMap.Strict as M 
import           Data.Monoid
import           Data.Maybe
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

toSubst :: RSubst r -> Subst
toSubst (Su m lm) = Su (M.map toType m) lm

toLists  :: RSubst r -> ([(TVar, RType r)], [(Location,Location)])
toLists (Su m lm) =  (M.toList m, M.toList lm)

fromLists :: [(TVar, RType r)] -> [(Location,Location)] -> RSubst r
fromLists l1 l2 = Su (M.fromList l1) (M.fromList l2)

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

instance Free a => Free (Heap a) where
  free = S.unions . map free . heapTypes

instance Substitutable r a => Substitutable r [a] where 
  apply = map . apply 

instance Substitutable r Location where
  apply (Su _ lsub) l = M.lookupDefault l l lsub

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
  free (TBd (TD _ α h t _ ))= foldr S.delete (free t) α

instance Substitutable () Fact where
  apply _ x@(PhiVar _)    = x
  apply θ (FunInst ts ls) = FunInst (map (apply θ <$>) ts) (map (apply θ <$>) ls)
  apply θ (LocInst l)     = LocInst (apply θ l)
  apply θ (Assume  t)     = Assume  $ apply θ t
  apply θ (AssumeH h)     = AssumeH $ apply θ h
  apply θ (Rename ls)     = Rename $ apply θ ls
  apply θ (WindInst l t αs ls) =
    WindInst (apply θ l) t (map (apply θ <$>) αs) (map (apply θ <$>) ls)
  apply θ (UnwindInst l t ls) = UnwindInst (apply θ l) t (map (apply θ <$>) ls)

instance (PP r, F.Reftable r) => Substitutable r (Fact_ r) where
  apply _ x@(PhiVar _)    = x
  apply θ (FunInst ts ls) = FunInst (map (apply θ <$>) ts) (map (apply θ <$>) ls)
  apply θ (LocInst l)     = LocInst (apply θ l)
  apply θ (Assume  t)     = Assume  $ apply θ t
  apply θ (AssumeH h)     = AssumeH $ apply θ h
  apply θ (Rename ls)     = Rename $ apply θ ls
  apply θ (WindInst l t αs ls) =
    WindInst (apply θ l) t (map (apply θ <$>) αs) (map (apply θ <$>) ls)
  apply θ (UnwindInst l t ls) = UnwindInst (apply θ l) t (map (apply θ <$>) ls)


instance Free Fact where
  free (PhiVar _)         = S.empty
  free (FunInst ts _)     = free . snd . unzip $ ts
  free (LocInst _)        = S.empty
  free (Assume t)         = free t
  free (AssumeH h)        = free h
  free (WindInst _ _ ts _) = free. snd . unzip $ ts
  free (UnwindInst _ _ _)  = S.empty
  free (Rename ls)        = S.empty

instance Free (Fact_ r) where
  free (PhiVar _)       = S.empty
  free (FunInst ts _)   = free . snd . unzip $ ts
  free (LocInst _)      = S.empty
  free (Assume t)       = free t
  free (AssumeH h)      = free h
  free (WindInst _ _ ts _) = free. snd . unzip $ ts
  free (UnwindInst _ _ _)  = S.empty
  free (Rename ls)      = S.empty
 
------------------------------------------------------------------------
-- appTy :: Subst_ r -> RType r -> RType r
------------------------------------------------------------------------
appTy (Su _ m) (TApp (TRef l) t z)    = TApp (TRef $ M.lookupDefault l l m) t z
appTy θ (TApp c ts z)                 = TApp c (apply θ ts) z 
appTy θ (TObj bs z)                   = TObj (map (\b -> B { b_sym = b_sym b, b_type = appTy θ $ b_type b } ) bs ) z
appTy (Su m _) t@(TVar α r)           = (M.lookupDefault t α m) `strengthen` r
appTy θ (TFun ts t h h' r)            = appTyFun θ ts t h h' r
appTy (Su ts ls) (TAll α t)           = apply (Su (M.delete α ts) ls) t 
appTy θ@(Su ts ls) (TBd (TD c α h t s)) = TBd $ TD c α (apply θ h) (apply (Su (foldr M.delete ts α) ls) t) s

appTyFun θ ts t h h' r =
  TFun (apply θ ts) (apply θ t) (go h) (go h') r
      where go            = heapFromBinds . map appBind . heapBinds 
            appBind (l,t) = (apply θ l, apply θ t)
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
        Just (TBd (TD _ vs _ bd _ )) -> apply (fromLists (zip vs acts) []) bd
        _                            -> error $ errorUnboundId id
    go (TApp c a r)            = TApp c (go <$> a) r
    go t@(TVar _ _ )           = t
    appTBi f (B s t)           = B s $ f t


-- | Unfold a top-level type definition once. 
-- Return @Right t@, where @t@ is the unfolded type if the unfolding is succesful.
-- This includes the case where the input type @t@ is not a type definition in
-- which case the same type is returned.
-- If it is a type literal for which no definition exists return 
-- @Left "<Error message>".

-- TODO: Make sure toplevel refinements are the same.
-------------------------------------------------------------------------------
unfoldMaybe :: (PP r, F.Reftable r) => Env (RType r) -> RType r -> Either String (RHeap r, RType r, RSubst r)
-------------------------------------------------------------------------------
unfoldMaybe env t@(TApp (TDef id) acts _) =
      case envFindTy (F.symbol id) env of
        Just (TBd (TD _ vs h bd _ )) -> Right $ let θ = fromLists (zip vs acts) []
                                                in (apply θ h, apply θ bd, θ)
        _                            -> Left  $ (printf "Failed unfolding: %s" $ ppshow t)
-- The only thing that is unfoldable is a TDef.
-- The rest are just returned as they are.
unfoldMaybe _ t                           = Right (heapEmpty, t, mempty)


-- | Force a successful unfolding
-------------------------------------------------------------------------------
unfoldSafe :: (PP r, F.Reftable r) => Env (RType r) -> RType r -> (RHeap r, RType r, RSubst r)
-------------------------------------------------------------------------------
unfoldSafe env = either error id . unfoldMaybe env

data ObjectAccess r = Access { ac_result :: RType r
                             , ac_cast   :: RType r
                             , ac_unfold :: Maybe (Id SourceSpan, RSubst r, RType r)
                             , ac_heap   :: Maybe (RHeap r)
                             } 
                      
accessNoUnfold t r = [Access { ac_result = r                      
                             , ac_cast   = t
                             , ac_unfold = Nothing
                             , ac_heap   = Nothing 
                             }
                     ]

-- Returns type to cast the current expression and the returned type
-------------------------------------------------------------------------------
dotAccessRef ::  (Ord r, PP r, F.Reftable r, F.Symbolic s, PP s) => 
  (Env (RType r), RHeap r) -> s -> RType r -> Maybe [ObjectAccess r]
-------------------------------------------------------------------------------
dotAccessRef (γ,σ) f (TApp (TRef l) _ _)
  = dotAccessBase γ f (heapRead "dotAccessRef" l σ)

dotAccessRef (γ,σ) f _ = Nothing

-------------------------------------------------------------------------------
dotAccessBase ::  (Ord r, PP r, F.Reftable r, F.Symbolic s, PP s) => 
  Env (RType r) -> s -> RType r -> Maybe [ObjectAccess r]
  -- (RType r, RType r)
-------------------------------------------------------------------------------
dotAccessBase _ f t@(TObj bs _) = 
  do  case find (match $ F.symbol f) bs of
        Just b -> Just $ accessNoUnfold t $ b_type b
        _      -> case find (match $ F.stringSymbol "*") bs of
                    Just b' -> Just $ accessNoUnfold t $ b_type b'
                    _       -> Just $ accessNoUnfold t tUndef
  where match s (B f _)  = s == f

dotAccessBase γ f t@(TApp c ts _ ) = go c
  where  go TUn      = dotAccessUnion γ f ts
         go TInt     = Just $ accessNoUnfold t tUndef
         go TBool    = Just $ accessNoUnfold t tUndef
         go TString  = Just $ accessNoUnfold t tUndef
         go TUndef   = Nothing
         go TNull    = Nothing
         go (TDef i) = dotAccessDef γ i f t -- dotAccess γ f $ unfoldSafe γ t
         go TTop     = error "dotAccess top"
         go TVoid    = error "dotAccess void"

dotAccessBase _ _ t@(TFun _ _ _ _ _) = Just $ accessNoUnfold t tUndef
dotAccessBase _ _ t               = error $ "dotAccessBase " ++ (ppshow t) 
                                
dotAccessDef γ i f t = (addUnfolded <$>) <$> dotAccessBase γ f t_unfold
  where  
    (σ_unfold, t_unfold, θ_unfold) = unfoldSafe γ t
    addUnfolded access             = 
      case (ac_heap access, ac_unfold access) of
        (Just x, Just y) -> error $ (printf "BUG: already unfolded and got %s %s" (ppshow x) (ppshow (fst3 y, thd3 y)))
        _                -> access { ac_heap   = Just σ_unfold
                                   , ac_unfold = Just (i, θ_unfold, t_unfold)
                                   , ac_cast   = t
                                   }

-- Accessing the @x@ field of the union type with @ts@ as its parts, returns
-- "Nothing" if accessing all parts return error, or "Just (ts, tfs)" if
-- accessing @ts@ returns type @tfs@. @ts@ is useful for adding casts later on.
-------------------------------------------------------------------------------
dotAccessUnion ::  (Ord r, PP r, F.Reftable r, F.Symbolic s, PP s) => 
  Env (RType r) -> s -> [RType r] -> Maybe [ObjectAccess r]  --  (RType r, RType r)
-------------------------------------------------------------------------------
dotAccessUnion γ f ts = concat <$> traverse (dotAccessBase γ f) ts
