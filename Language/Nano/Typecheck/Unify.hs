{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Nano.Typecheck.Unify ( 
  
  -- * Unification 
    unify
  , unifys
  , unifyHeaps

  -- * Heap Substs
  , safeHeapSubst
  , safeHeapSubstWith

  ) where 

-- import           Text.PrettyPrint.HughesPJ
import           Language.ECMAScript3.PrettyPrint
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types as F
import           Language.Nano.Errors 
import           Language.Nano.Env
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Compare

import           Control.Applicative ((<$>))
-- import           Control.Monad
import           Data.Maybe (fromJust)
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M 
import           Data.Monoid
import qualified Data.List           as L
import           Text.Printf 
-- import           Debug.Trace
import           Language.Nano.Misc (fst4)


-----------------------------------------------------------------------------
-- Unification --------------------------------------------------------------
-----------------------------------------------------------------------------

-- | Unify types @t@ and @t'@, using @θ@ as the current substitution and @env@
-- as the current type definition environment.
-----------------------------------------------------------------------------
unify :: (PP r, F.Reftable r, Ord r) => 
  Env (RType r) -> RSubst r -> RType r -> RType r -> Either String (RSubst r)
-----------------------------------------------------------------------------
unify _ θ (TApp (TRef l1) _ _) (TApp (TRef l2) _ _) =
  -- Right $ if l1' == l2' then θ else θ'
  unifyLocs θ l1 l2
    -- where l1'      = apply θ l1
    --       l2'      = apply θ l2
    --       θ'       = θ `mappend` Su M.empty (M.singleton l1' l2')
        
unify _ θ t@(TApp _ _ _) t'@(TApp _ _ _) 
  | any isTop [t,t']                    = Right θ

unify env θ (TFun xts t _ _ _) (TFun xts' t' _ _ _) = 
  unifys env θ (t: (b_type <$> xts)) (t': (b_type <$> xts'))

-- TODO: Cycles
unify env θ (TApp d@(TDef _) ts _) (TApp d'@(TDef _) ts' _)
  | d == d'                             = unifys env θ ts ts'

unify _  θ (TVar α _)     (TVar β _)    = varEql θ α β 
unify _  θ (TVar α _)     t             = varAsn θ α t 
unify _  θ t              (TVar α _)    = varAsn θ α t

-- unify env θ t@(TApp (TDef _) _ _) t'    = unify env θ (unfoldSafe env t) t'
-- unify env θ t t'@(TApp (TDef _) _ _)    = unify env θ t (unfoldSafe env t')

-- List[A] + Null `unif` List[T0] + Null => A `unif` T0
-- TODO: make sure other nothing weird is going on with TVars,
-- e.g.  List[A] + B `unif` ... => this should not even be allowed!!!
unify env θ t t' | any isUnion [t,t']     = 
  (uncurry $ unifys env θ) $ unzip $ fst3 -- $ tracePP "unify union"
    $ unionPartsWithEq (unifEq env θ) t t'

unify _ _ (TBd _) _   = error $ bugTBodiesOccur "unify"
unify _ _ _ (TBd _)   = error $ bugTBodiesOccur "unify"

-- only unify if the objects align perfectly
unify env θ (TObj bs1 _) (TObj bs2 _) 
  | s1s == s2s 
  = unifys env θ (b_type <$> L.sortBy ord bs1) (b_type <$> L.sortBy ord bs2)
  | otherwise 
  = return θ
    where
      s1s = L.sort $ b_sym <$> bs1 
      s2s = L.sort $ b_sym <$> bs2
      ord b b' = compare (b_sym b) (b_sym b')

-- For the rest of the cases, blindly return the subst
-- Defer all other checks for later
unify _ θ _ _         = Right θ

-- unifyHeapLocations (γ,σ) θ =
--   foldl joinSub (Right θ) bs
--     where bs = heapBinds σ
--           joinSub s@(Right θ) (l,t) =
--             if heapMem (apply θ l) σ then
--               unify (γ,σ) θ t (heapRead (apply θ l) σ)
--             else 
--               s
--           joinSub s _ = s
          
-- Unification may have resulted in heap locations that need to be merged
safeHeapSubstWith f γ θ σ = foldl joinLoc heapEmpty . map (apply' θ) . heapBinds $ σ
    where joinLoc σ (l,t) = heapAddWith (f γ) l t σ
          apply' θ (l,(Right t)) = (apply θ l, Right $ apply θ t)
          apply' _ l             = l

safeHeapSubst = safeHeapSubstWith safeAdd
    where safeAdd γ (Right t1) (Right t2)   = Right $ fst4 $ compareTs γ t1 t2
          safeAdd _ _          _            = error "Bug in unifyHeap"

{-unify' γ θ t t' = unify γ θ (trace (printf "unify: %s - %s" (show t) (show t')) t) t' -}

-- TODO: cycles
unifEq _ _ (TApp d@(TDef _) _ _) (TApp d'@(TDef _) _ _) | d == d' = True
-- unifEq γ t@(TApp (TDef _) _ _) t' = unifEq γ (snd $ unfoldSafe γ t) t'
-- unifEq γ t t'@(TApp (TDef _) _ _) = unifEq γ t (snd $ unfoldSafe γ t')
unifEq _ θ (TApp (TRef l) _ _) (TApp (TRef m) _ _)
  | unassignedRef l θ || unassignedRef m θ = True
  | otherwise                              = l == m
unifEq γ _ t t'                     = equiv γ t t'

-----------------------------------------------------------------------------
unifys ::  (PP r, F.Reftable r, Ord r) =>  
  Env (RType r) -> RSubst r -> [RType r] -> [RType r] -> Either String (RSubst r)
-----------------------------------------------------------------------------
unifys env θ xs ys = tracePP msg $ unifys' env θ xs ys
   where
     msg      = printf "unifys: [xs = %s] [ys = %s] [θ = %s]"  (ppshow xs) (ppshow ys) (ppshow θ)

unifys' γ θ ts ts' 
  | nTs == nTs' = go γ θ ts ts'
  | otherwise   = Left $ errorUnification ts ts'
  where 
    nTs                      = length ts
    nTs'                     = length ts'
    -- go γ θ ts ts' = foldl safeJoin (Right θ) $ zipWith (unify γ θ) ts ts'
    go γ θ ts ts' = foldl foldU (Right θ) $ zip ts ts'
    -- Only allow joining unifications where the common keys map to identical
    -- types
    foldU (Left l) _         = Left l
    foldU (Right θ) (t1, t2) = unify γ θ (apply θ t1) (apply θ t2)
    safeJoin (Right θ) (Right θ')
      | check θ θ' = Right $ (θ `mappend` θ')
      | otherwise  = Left  $ printf "Cannot join substs: %s\nand\n%s\n"
                               (ppshow θ) (ppshow θ')
    safeJoin (Left l        ) _                  = Left l
    safeJoin _                (Left l        )   = Left l
                               
check θ@(Su m l) θ'@(Su m' l') = vs == vs'
  where vs  = map (toType . apply θ' <$>) $ (`M.lookup` m ) <$> ks
        vs' = map (toType . apply θ  <$>) $ (`M.lookup` m') <$> ks
        ks  = M.keys $ M.intersection (clr tVar m) (clr tVar m')
        clr f = M.filterWithKey (\k v -> f k /= v)

-----------------------------------------------------------------------------
unifyHeaps :: (PP r, F.Reftable r, Ord r) => 
  Env (RType r) -> RSubst r -> RHeap r -> RHeap r -> Either String (RSubst r)
-----------------------------------------------------------------------------
unifyHeaps env θ σ1 σ2 = unifyHeaps' env (Right θ) bs1 bs2
  where
    bs1 = heapBinds σ1
    bs2 = heapBinds σ2
    
-----------------------------------------------------------------------------
unifyHeaps' :: (PP r, F.Reftable r, Ord r) =>
  Env (RType r) -> Either String (RSubst r) -> [(Location, RType r)]
  -> [(Location, RType r)] -> Either String (RSubst r)
-----------------------------------------------------------------------------
unifyHeaps' _ r@(Left _)  _   _   = r
unifyHeaps' _ r           []  _   = r
unifyHeaps' _ r           _   []  = r
unifyHeaps' γ r@(Right θ) bs1 bs2 = 
  if common == [] then
    r
  else
    unifyHeaps' γ (unifys γ θ t1s t2s) bs1'' bs2''
  where
    ls        = L.nub $ ls1 ++ ls2
    bs1'      = map (\(l,t) -> (apply θ l, apply θ t)) bs1
    bs2'      = map (\(l,t) -> (apply θ l, apply θ t)) bs2
    ls1       = map fst bs1'
    ls2       = map fst bs2'

    memBoth l = apply θ l `elem` ls1 && apply θ l `elem` ls2
    common    = L.nub $ L.filter memBoth ls

    t1s       = (fromJust . flip L.lookup bs1') <$> common
    t2s       = (fromJust . flip L.lookup bs2') <$> common

    bs1''      = filter (not . (`elem` common) . fst) bs1'
    bs2''      = filter (not . (`elem` common) . fst) bs2'


-----------------------------------------------------------------------------
varEql :: (PP r, F.Reftable r, Ord r) => 
  RSubst r -> TVar -> TVar -> Either String (RSubst r)
-----------------------------------------------------------------------------
varEql θ α β =  
  case varAsn θ α $ tVar β of
    Right θ' -> Right θ'
    Left  s1 -> 
      case varAsn θ β $ tVar α of
        Right θ'' -> Right θ''
        Left  s2  -> Left (s1 ++ "\n OR \n" ++ s2)


-----------------------------------------------------------------------------
varAsn ::  (PP r, F.Reftable r, Ord r) => 
  RSubst r -> TVar -> RType r -> Either String (RSubst r)
-----------------------------------------------------------------------------
varAsn θ α t 
  -- Check if previous substs are sufficient 
  | t == apply θ (tVar α)  = Right $ θ 
  -- We are not even checking if t is a subtype of `tVar α`, i.e.:
  -- unifying A with A + B will fail!
  | t == tVar α            = Right $ θ 
  | α `S.member` free t    = Left  $ errorOccursCheck α t 
  | unassigned α θ         = Right $ θ `mappend` (Su (M.singleton α t) (locSub θ))
  | otherwise              = Left  $ errorRigidUnify α t

unifyLocs θ l1 l2
  | apply θ l1 == apply θ l2 = Right $ θ
  | unassignedRef l1 θ     = Right $ θ `mappend` (Su (tySub θ) (M.singleton l1 l2))
  | unassignedRef l2 θ     = Right $ θ `mappend` (Su (tySub θ) (M.singleton l2 l1))
  | otherwise              = Left  $ printf "Unable to unify rigid locations %s and %s" l1 l2
  
unassigned α (Su m _) = M.lookup α m == Just (tVar α)

unassignedRef l (Su _ m) = M.lookup l m == Just l
