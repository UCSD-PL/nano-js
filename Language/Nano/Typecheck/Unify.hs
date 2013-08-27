{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Nano.Typecheck.Unify ( 
  
  -- * Unification 
  unify, unifys

  ) where 

-- import           Text.PrettyPrint.HughesPJ
-- import           Language.ECMAScript3.PrettyPrint
import           Language.Fixpoint.Misc
-- import qualified Language.Fixpoint.Types as F
import           Language.Nano.Errors 
import           Language.Nano.Env
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Compare

import           Control.Applicative ((<$>))
-- import           Control.Monad
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
unify :: (Env Type, BHeap) -> Subst -> Type -> Type -> Either String (Subst, BHeap)
-----------------------------------------------------------------------------
-- TODO: is this right??
unify (γ,σ) θ (TApp (TRef l1) _ _) (TApp (TRef l2) _ _) =
    if l1' == l2' then
        Right $ (θ,σ)
    else
        unifyHeapLocations (γ,σ) θ' l1 l2
    where l1'      = apply θ l1
          l2'      = apply θ l2
          θ'       = θ `mappend` Su M.empty (M.singleton l1' l2')
        
unify (γ,σ) θ t@(TApp _ _ _) t'@(TApp _ _ _) 
  | any isTop [t,t']                    = Right $ (θ,σ)

unify env θ (TFun xts t _ _ _) (TFun xts' t' _ _ _) = 
  unifys env θ (t: (b_type <$> xts)) (t': (b_type <$> xts'))

-- TODO: Cycles
unify env θ (TApp d@(TDef _) ts _) (TApp d'@(TDef _) ts' _)
  | d == d'                             = unifys env θ ts ts'

unify (γ,σ) θ t@(TApp (TDef _) _ _) t'  = unify (γ,σ) θ (unfoldSafe γ t) t'

unify (γ,σ) θ t t'@(TApp (TDef _) _ _)  = unify (γ,σ) θ t (unfoldSafe γ t')
-- TODO: fix                                          
unify (γ,σ) θ (TVar α _)     (TVar β _) = case varEql θ α β of
                                            Right θ -> Right (θ,σ)
                                            Left m  -> Left m
unify (γ,σ) θ (TVar α _)     t          = case varAsn θ α t of
                                            Right θ -> Right (θ,σ)
                                            Left m  -> Left m
unify (γ,σ) θ t              (TVar α _) = case varAsn θ α t of
                                            Right θ -> Right (θ,σ)
                                            Left m  -> Left m

-- List[A] + Null `unif` List[T0] + Null => A `unif` T0
-- TODO: make sure other nothing weird is going on with TVars,
-- e.g.  List[A] + B `unif` ... => this should not even be allowed!!!
unify env θ t t' | any isUnion [t,t']     = 
  (uncurry $ unifys env θ) $ unzip $ fst3 -- $ tracePP "unify union"
    $ unionPartsWithEq (unifEq env) t t'

unify _ _ (TBd _) _   = error $ bugTBodiesOccur "unify"
unify _ _ _ (TBd _)   = error $ bugTBodiesOccur "unify"

-- only unify if the objects align perfectly
unify env@(γ,σ) θ (TObj bs1 _) (TObj bs2 _) 
  | s1s == s2s 
  = unifys env θ (b_type <$> L.sortBy ord bs1) (b_type <$> L.sortBy ord bs2)
  | otherwise 
  = return (θ,σ)
    where
      s1s = L.sort $ b_sym <$> bs1 
      s2s = L.sort $ b_sym <$> bs2
      ord b b' = compare (b_sym b) (b_sym b')

-- For the rest of the cases, blindly return the subst
-- Defer all other checks for later
unify (γ,σ) θ _ _         = Right $ (θ,σ)

unifyHeapLocations (γ,σ) θ l1 l2 = foo γ θ σ
  -- Right (θ, applyUnifyingSub γ θ σ)
  -- case unify (γ,σ) θ t1 t2 of
  --   Left m         -> Left m
  --   Right (θ', σ') -> Right (θ', applyUnifyingSub γ θ' $ delLocation l1 σ')
  --   where
  --     t1      = rdLocation l1 σ
  --     t2      = rdLocation l2 σ

-- applyUnifyingSub γ θ σ = foldl safeAdd emp σ'
--     where σ'              = map (apply θ) $ hbinds σ
--           safeAdd h (l,t) = addLocationWith (\t1 t2 -> if eqType γ t1 t2 then t1 else mkUnion [t1,t2]) l t h

foo γ θ σ =  foldl (\sub (l,t) ->
                    case sub of
                      Right (θ,σ) ->
                          if hmem (apply θ l) σ then
                              unify (γ,σ) θ t (rdLocation (apply θ l) σ)
                          else
                              sub
                      Left m -> Left m) (Right (θ,σ)) bs
    where bs = hbinds σ
          
{-unify' γ θ t t' = unify γ θ (trace (printf "unify: %s - %s" (show t) (show t')) t) t' -}

-- TODO: cycles
unifEq _ (TApp d@(TDef _) _ _) (TApp d'@(TDef _) _ _) | d == d' = True
unifEq (γ,σ) t@(TApp (TDef _) _ _) t' = unifEq (γ,σ) (unfoldSafe γ t) t'
unifEq (γ,σ) t t'@(TApp (TDef _) _ _) = unifEq (γ,σ) t (unfoldSafe γ t')
unifEq (γ,σ) t t'                     = equiv γ t t'

-----------------------------------------------------------------------------
unifys ::  (Env Type, BHeap) -> Subst -> [Type] -> [Type] -> Either String (Subst, BHeap)
-----------------------------------------------------------------------------
unifys env θ xs ys =   tracePP msg $ unifys' env θ xs ys
   where
     msg      = printf "unifys: [xs = %s] [ys = %s]"  (ppshow xs) (ppshow ys)

unifys' env@(γ,σ) θ ts ts' 
  | nTs == nTs' = go env θ ts ts'
  | otherwise   = Left $ errorUnification ts ts'
  where 
    nTs                      = length ts
    nTs'                     = length ts'
    go (γ,σ) θ ts ts' = -- applyHeapSub γ $ 
                        foldl safeJoin (Right $ (θ,σ)) $ zipWith (unify (γ,σ) θ) ts ts'
    -- applyHeapSub γ (Right (θ,σ)) = Right $ 
    --     (θ, foldl (\σ' (l,t) -> addLocationWith (\t1 t2 -> fst4 $ compareTs γ (tracePP "comparing t1" t1) (tracePP "comparing t2" t2)) l t σ') emp $ tracePP "the list" $ map (apply (tracePP "the sub" θ)) $ hbinds $ tracePP "the heap" σ)
    -- Only allow joining unifications where the common keys map to identical
    -- types
    safeJoin (Right (θ,σ)) (Right (θ',σ'))
      | check θ θ' = Right $ (θ `mappend` θ', σ')
      | otherwise  = Left  $ printf "Cannot join substs: %s\nand\n%s\n"
                               (ppshow θ) (ppshow θ')
    safeJoin (Left l        ) _                  = Left l
    safeJoin _                (Left l        )   = Left l
                               
checkHeaps θ σ σ' = σ == σ' -- TODO for now...?
    
check (Su m _) (Su m' _) = vs == vs'
  where vs  = (`M.lookup` m ) <$> ks
        vs' = (`M.lookup` m') <$> ks
        ks  = M.keys $ M.intersection (clr m) (clr m')
        clr = M.filterWithKey (\k v -> tVar k /= v)


-----------------------------------------------------------------------------
varEql :: Subst -> TVar -> TVar -> Either String Subst
-----------------------------------------------------------------------------
varEql θ α β =  
  case varAsn θ α $ tVar β of
    Right θ' -> Right θ'
    Left  s1 -> 
      case varAsn θ β $ tVar α of
        Right θ'' -> Right θ''
        Left  s2  -> Left (s1 ++ "\n OR \n" ++ s2)


-----------------------------------------------------------------------------
varAsn :: Subst -> TVar -> Type -> Either String Subst
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
  
unassigned α (Su m _) = M.lookup α m == Just (tVar α)


