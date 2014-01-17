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
  , unfoldFirst
  , unfoldMaybe
  , unfoldSafe
  , unfoldMaybeEnv -- Retain heap binders
  , unfoldSafeEnv
  
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

instance (PP r, PP b, F.Reftable r, Substitutable r b) =>
    Substitutable r (Heap b) where
  apply θ h =
      heapFromBinds "apply" $ map (\(l, t) -> (apply θ l,apply θ t)) $ heapBinds h

instance (PP r, PP b, F.Reftable r, Substitutable r b) =>
    Substitutable r (Heap (Id b)) where
  apply θ h =
      heapFromBinds "apply" $ map (\(l, i) -> (apply θ l, i)) $ heapBinds h

instance (Substitutable r a, Substitutable r b) => Substitutable r (a,b) where 
  apply f (x,y) = (apply f x, apply f y)

instance (PP r, Ord r, F.Reftable r) => Substitutable r (RType r) where 
  apply θ t = appTy θ t
--     where 
--       msg   = printf "apply [θ = %s] [t = %s]" (ppshow θ) (ppshow t)
instance (PP r, Ord r, F.Reftable r) => Substitutable r (PRef Type r (RType r)) where
  apply θ  (PMono xts r) = PMono ((toType . appTy θ . ofType <$>) <$> xts) r
  apply θ' (PPoly xts t) = PPoly ((toType . appTy θ . ofType <$>) <$> xts) (apply θ t)
    where
      (vts, ls) = toLists θ'
      vts'      = [(v, setRTypeR t F.top) | (v, t) <- vts] :: [(TVar, RType r)]
      θ         = fromLists vts' ls :: RSubst r

instance (PP r, Ord r, F.Reftable r) => Substitutable r (PVar Type) where
  apply θ (PV s l t as) = PV s l (apply θ' t) (mapFst3 (apply θ') <$> as)
    where θ'       = fromLists (fmap toType <$> vs) ls
          (vs, ls) = toLists θ

instance (PP r, Ord r, F.Reftable r) => Substitutable r (Bind r) where 
  apply θ (B z t) = B z $ appTy θ t

instance Free (RType r) where
  free (TApp _ ts ps _)          = S.unions   $ free <$> ts
  free (TVar α _)                = S.singleton α 
  free (TFun xts t h h' _)       = S.unions   $ free <$> funTs (t:xts, h, h')
  free (TAll α t)                = S.delete α $ free t 
  free (TObj bs _)               = S.unions   $ free <$> b_type <$> bs
  free (TBd (TD _ _ α _ h t _ )) = foldr S.delete (free t) α

instance (Free t, Free m) => Free (PRef t s m) where
  free (PMono xts _) = S.unions $ map (free . snd) xts
  free (PPoly xts t) = S.unions $ free t:map (free . snd) xts

funTs (xts, h, h') = ts                               
    where ts = (b_type <$> xts)
             ++ heapTypes (b_type <$> h)
             ++ heapTypes (b_type <$> h')

instance Substitutable () Fact where
  apply _ x@(PhiVar _)    = x
  apply θ (FunInst ts ls) = FunInst (map (apply θ <$>) ts) (map (apply θ <$>) ls)
  apply θ (LocInst l)     = LocInst (apply θ l)
  apply θ (WorldInst l)   = WorldInst (apply θ l)
  apply θ (Assume  t)     = Assume  $ apply θ t
  apply θ (AssumeH h)     = AssumeH $ apply θ h
  apply θ (Rename ls)     = Rename $ apply θ ls
  apply θ (Delete ls)     = Delete $ apply θ ls
  apply θ (WindInst l wls t αs ls) =
    WindInst (apply θ l) (apply θ wls) t (map (apply θ <$>) αs) (map (apply θ <$>) ls)
  apply θ (UnwindInst l t ls) = UnwindInst (apply θ l) t (map (apply θ <$>) ls)

instance (PP r, Ord r, F.Reftable r) => Substitutable r (Fact_ r) where
  apply _ x@(PhiVar _)    = x
  apply θ (FunInst ts ls) = FunInst (map (apply θ <$>) ts) (map (apply θ <$>) ls)
  apply θ (LocInst l)     = LocInst (apply θ l)
  apply θ (WorldInst l)   = WorldInst (apply θ l)
  apply θ (Assume  t)     = Assume  $ apply θ t
  apply θ (AssumeH h)     = AssumeH $ apply θ h
  apply θ (Rename ls)     = Rename $ apply θ ls
  apply θ (Delete ls)     = Delete $ apply θ ls
  apply θ (WindInst l wls t αs ls) =
    WindInst (apply θ l) (apply θ wls) t (map (apply θ <$>) αs) (map (apply θ <$>) ls)
  apply θ (UnwindInst l t ls) = UnwindInst (apply θ l) t (map (apply θ <$>) ls)


instance Free Fact where
  free (PhiVar _)         = S.empty
  free (FunInst ts _)     = free . snd . unzip $ ts
  free (LocInst _)        = S.empty
  free (WorldInst _)      = S.empty
  free (Assume t)         = free t
  free (AssumeH h)        = free h
  free (WindInst _ _ _ ts _) = free. snd . unzip $ ts
  free (UnwindInst _ _ _)  = S.empty
  free (Rename ls)        = S.empty
  free (Delete ls)        = S.empty

instance Free (Fact_ r) where
  free (PhiVar _)       = S.empty
  free (FunInst ts _)   = free . snd . unzip $ ts
  free (LocInst _)      = S.empty
  free (WorldInst _)    = S.empty
  free (Assume t)       = free t
  free (AssumeH h)      = free h
  free (WindInst _ _ _ ts _) = free. snd . unzip $ ts
  free (UnwindInst _ _ _)  = S.empty
  free (Rename ls)      = S.empty
  free (Delete ls)      = S.empty
 
------------------------------------------------------------------------
-- appTy :: Subst_ r -> RType r -> RType r
------------------------------------------------------------------------
appTy θ@(Su _ m) (TApp (TRef l) t rs z) = TApp (TRef $ M.lookupDefault l l m) t (apply θ rs) z
appTy θ (TApp TUn ts rs z)            = mkUnionR rs z (nub $ apply θ ts)
appTy θ (TApp c ts rs z)              = TApp c (apply θ ts) (apply θ rs) z 
appTy θ (TObj bs z)                   = TObj (map (\b -> B { b_sym = b_sym b, b_type = appTy θ $ b_type b } ) bs ) z
appTy (Su m _) t@(TVar α r)           = (M.lookupDefault t α m) `strengthen` r
appTy θ (TFun ts t h h' r)            = appTyFun θ ts t h h' r
appTy (Su ts ls) (TAll α t)           = apply (Su (M.delete α ts) M.empty) t  -- Assuming all locations are always quantified
appTy θ@(Su ts ls) (TBd (TD c v α π h t s)) = TBd $ TD c v α (apply θ π) (apply θ h) (apply (Su (foldr M.delete ts α) ls) t) s

-- Avoid capturing all locs in subs on funs for now
appTyFun θ ts t h h' r =
  TFun (apply θ ts) (apply θ t) (go h) (go h') r
      where go            = heapFromBinds "appTyFun" . map appBind . heapBinds 
            appBind (l,t) = (apply θ l, apply θ t)
-- | Unfold the FIRST TDef at any part of the type @t@.
-------------------------------------------------------------------------------
unfoldFirst :: (PP r, Ord r, F.Reftable r) => Env (RType r) -> RType r -> RType r
-------------------------------------------------------------------------------
unfoldFirst env t = go t
  where 
    go (TFun its ot h h' r)    = TFun (goB <$> its) (goB ot) (goB <$> h) (goB <$> h') r
    go (TObj bs r)             = TObj (goB <$> bs) r
    go (TBd  _)                = error "unfoldTDefDeep: there should not be a TBody here"
    go (TAll v t)              = TAll v $ go t
    go (TApp (TDef id) acts _ _) = 
      case envFindTy (F.symbol id) env of
        Just (TBd (TD _ _ vs πs _ bd _ )) -> apply (fromLists (zip vs acts) []) bd
        _                                 -> error $ errorUnboundId id
    go (TApp c a rs r)         = TApp c (go <$> a) rs r
    go t@(TVar _ _ )           = t
    goB (B s t)                = B s $ go t

-- | Unfold a top-level type definition once. 
-- Return @Right t@, where @t@ is the unfolded type if the unfolding is succesful.
-- This includes the case where the input type @t@ is not a type definition in
-- which case the same type is returned.
-- If it is a type literal for which no definition exists return 
-- @Left "<Error message>".

-- TODO: Make sure toplevel refinements are the same.
-------------------------------------------------------------------------------
unfoldMaybeEnv :: (PP r, Ord r, F.Reftable r) =>
  Env (RType r) -> RType r -> Either String (RHeapEnv r, Bind r, RSubst r)
-------------------------------------------------------------------------------
unfoldMaybeEnv env t@(TApp (TDef id) acts _ _) =
      case envFindTy (F.symbol id) env of
        Just (TBd (TD _ s vs πs h bd _ )) ->
          Right $ (h, B s bd, θ) where θ = fromLists (zip vs acts) []
        _                                 ->
          Left  $ (printf "Failed unfolding: %s" $ ppshow t)

-- The only thing that is unfoldable is a TDef.
-- The rest are just returned as they are.
unfoldMaybeEnv _ t                           = Left $ (printf "Attempt to unfold: %s" $ ppshow t)

-------------------------------------------------------------------------------
unfoldMaybe :: (PP r, Ord r, F.Reftable r) =>
  Env (RType r) -> RType r -> Either String (RHeap r, RType r, RSubst r)
-------------------------------------------------------------------------------
unfoldMaybe env t = toType <$> unfoldMaybeEnv env t
    where toType (h,b,θ) = (b_type <$> h, b_type $ b, θ) 

-- | Force a successful unfolding
-------------------------------------------------------------------------------
unfoldSafeEnv :: (PP r, Ord r, F.Reftable r) =>
  Env (RType r) -> RType r -> (RHeapEnv r, Bind r, RSubst r)
-------------------------------------------------------------------------------
unfoldSafeEnv env = either error id . unfoldMaybeEnv env


-- | Force a successful unfolding
-------------------------------------------------------------------------------
unfoldSafe :: (PP r, Ord r, F.Reftable r) =>
  Env (RType r) -> RType r -> (RHeap r, RType r, RSubst r)
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
dotAccessRef (γ,σ) f (TApp (TRef l) _ _ _)
  = dotAccessBase γ f $ tracePP "dotAccessRef" (heapRead "dotAccessRef" l $ tracePP "dotAccessRef heap" σ)

dotAccessRef (γ,σ) f _ = Nothing

-------------------------------------------------------------------------------
dotAccessBase ::  (Ord r, PP r, F.Reftable r, F.Symbolic s, PP s) => 
  Env (RType r) -> s -> RType r -> Maybe [ObjectAccess r]
-------------------------------------------------------------------------------
dotAccessBase _ f t@(TObj bs _) = 
  do  case find (match $ F.symbol f) bs of
        Just b -> Just $ accessNoUnfold t $ b_type b
        _      -> case find (match $ F.stringSymbol "*") bs of
                    Just b' -> Just $ accessNoUnfold t $ b_type b'
                    _       -> Just $ accessNoUnfold t tUndef
  where match s (B f _)  = s == f

dotAccessBase γ f t@(TApp c ts _ _) = go c
  where  go TUn      = dotAccessUnion γ f ts
         go TInt     = Just $ accessNoUnfold t tUndef
         go TBool    = Just $ accessNoUnfold t tUndef
         go TString  = Just $ accessNoUnfold t tUndef
         go TUndef   = Nothing
         go TNull    = Nothing
         go (TDef i) = dotAccessDef γ i f t -- dotAccess γ f $ unfoldSafe γ t
         go TTop     = error "dotAccess top"
         go TVoid    = error "dotAccess void"
         go c        = error $ "dotAccess " ++ ppshow c

dotAccessBase _ _ t@(TFun _ _ _ _ _) = Just $ accessNoUnfold t tUndef
dotAccessBase _ _ t               = error $ "dotAccessBase " ++ (ppshow t) 
                                
dotAccessDef γ i f t = (addUnfolded <$>) <$> dotAccessBase γ f t_unfold
  where  
    (σ_unfold, t_unfold, θ_unfold) = unfoldSafe γ $ tracePP "dotAccessDef unfolding" t
    addUnfolded access             = 
      case (ac_heap access, ac_unfold access) of
        (Just x, Just y) -> err x y
        _                -> access { ac_heap   = Just σ_unfold
                                   , ac_unfold = Just (i, θ_unfold, t_unfold)
                                   , ac_cast   = t
                                   }
    err x y = error $ printf "BUG: already unfolded %s and got %s %s"
                             (ppshow x) (ppshow (fst3 y)) (ppshow (thd3 y))

-- Accessing the @x@ field of the union type with @ts@ as its parts, returns
-- "Nothing" if accessing all parts return error, or "Just (ts, tfs)" if
-- accessing @ts@ returns type @tfs@. @ts@ is useful for adding casts later on.
-------------------------------------------------------------------------------
dotAccessUnion ::  (Ord r, PP r, F.Reftable r, F.Symbolic s, PP s) => 
  Env (RType r) -> s -> [RType r] -> Maybe [ObjectAccess r]  --  (RType r, RType r)
-------------------------------------------------------------------------------
dotAccessUnion γ f ts = concat <$> traverse (dotAccessBase γ f) ts
