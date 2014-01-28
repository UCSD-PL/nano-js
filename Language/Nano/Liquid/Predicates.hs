module Language.Nano.Liquid.Predicates where

import Data.List
import Text.Printf                        (printf)
import Control.Applicative
import Text.Parsec.Pos
import Language.ECMAScript3.Syntax
import Language.ECMAScript3.Parser        (SourceSpan (..))
import Language.Nano.Types           hiding (Loc)
import Language.Nano.Typecheck.Types
import Language.Nano.Typecheck.Heaps
import Language.Nano.Liquid.Types
import Language.Nano.Errors

import Language.Fixpoint.Misc
import Language.Fixpoint.Types as F
import Language.Fixpoint.PrettyPrint

-- | Handy functions for dealing with (abstract) predicates. Shamelessly
-- | stolen from LiquidHaskell

-------------------------------------------------------------------------------
-----------------------------  Predicate Replacement --------------------------
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- replacePredsWithRefs :: T -> T -> T
-------------------------------------------------------------------------------
replacePredsWithRefs (p, r) (U (Reft(v, rs)) (Pr ps)) 
  = U (Reft (v, rs ++ rs')) (Pr ps2)
  where rs'              = r . (v,) . pv_as <$> ps1
        (ps1, ps2)       = partition (==p) ps

-------------------------------------------------------------------------------
replacePreds :: RefType -> [(PVar Type, Ref RReft)] -> RefType
-------------------------------------------------------------------------------
replacePreds = foldl' go
  where go z (π, t@(PPoly _ _)) = substPred (π, t) z
        go _ (_, PMono _ _)     = error "replacePreds on PMono"
                                 
-------------------------------------------------------------------------------
-- make instance of some class? like Susbtitutable?
substPredVarSorts :: RefType -> RefType
-------------------------------------------------------------------------------
substPredVarSorts t = foldl (\t π -> mapTys (substPredVarSort π) t) t πs
  where (_,πs,t') = bkAll t 
                    
substPredVarSort π t@(TApp c ts rs r) 
  = tracePP (printf "substPredVarSort (%s)" (ppshow t)) $ TApp c ts (go <$> rs) r
  where go (PMono ss (U r (Pr [π']))) 
          | pv_sym π == pv_sym π' = PMono [(y,x) | (x,y,z) <- pv_as π] $ U r (Pr [πn])
        go r                      = r
        πn                        = π { pv_as = [((),y,z) | (_,y,z) <- pv_as π]
                                      , pv_ty = ()
                                      }
                                    
substPredVarSort _ t = t

-- substPredVarSort π (TApp c ts rs r) 
  -- = TApp c ts' rs' r'
  --   where
  --     ts' = substPredVarSort π <$> ts
  --     rs' = substPredVarSortRef π <$> rs
  --     r'  = substPredVarSortReft π <$> r

-- substPredVar π (TVar v r)           = TVar v $ substPredVarRef π r
-- substPredVar π (TFun bs rb hi ho r) =   
-- substPredVar π t@(TAllP π' t') 
--   | pv_sym π == pv_sym π' = t
--   | otherwise             = TAllP π' $ substPredVar π t'
                            

-------------------------------------------------------------------------------
substPred :: (PVar Type, Ref RReft) -> RefType -> RefType
-------------------------------------------------------------------------------
substPred (π, PPoly ss (TVar v1 r1)) t@(TVar v2 r2)
  | isPredInReft && v1 == v2 = TVar v1 $ meetListWithPSubs πs ss r1 r2'
  | isPredInReft             = errorstar $ "substPred TVar mismatch" ++ show (v1, v2)
  | otherwise                = t
  where
    (r2', πs)    = splitPVar π r2
    isPredInReft = not $ null πs

substPred su@(π, _) t@(TApp c ts rs r)
  | null πs   = t'
  | otherwise = substRCon su t' πs r2'
  where
    t' = tracePP (printf "substPred TApp(%s)" (ppshow t)) $ TApp c (substPred su <$> ts) (substPredP su <$> rs) r
    (r2', πs) = splitPVar π r

substPred su (TFun xts xt hi ho r)
  = TFun (substPredBind su <$> xts)
         (substPredBind su     xt)
         (substPredBind su <$> hi)
         (substPredBind su <$> ho)
         r

substPred su (TObj xts r)
  = TObj (substPredBind su <$> xts) r

substPred (_, p) t = error $ printf "substPred: TBD (%s, %s)" (ppshow p) (ppshow t)

substPredBind su (B x t) = B x $ substPred su t

substRCon :: (PVar Type, Ref RReft) -> RefType -> [PVar ()] -> RReft -> RefType 
substRCon (_, PPoly ss t@(TApp c1 ts1 rs1 r1)) t'@(TApp c2 ts2 rs2 _) πs r2'
  | c1 == c2           = TApp c1 ts rs $ meetListWithPSubs πs ss r1 r2'
  | otherwise          = errorstar $ printf "substRCon: unexpected %s/%s" (ppshow t) (ppshow t')
  where ts             = safeZipWith "substRCon"  strSub  ts1 ts2
        rs             = safeZipWith "substRcon2" strSubR rs1 rs2
        strSub r1 r2   = meetListWithPSubs πs ss r1 r2
        strSubR r1 r2  = meetListWithPSubsRef πs ss r1 r2

substRCon su t _ _        = errorstar $ printf "substRCon (%s)(%s)" (ppshow $ fmap show su) (ppshow t)

substPredP :: (PVar Type, Ref RReft) -> Ref RReft -> Ref RReft
substPredP su@(p, PPoly ss tt) (PPoly s t)
  = PPoly ss' $ substPred su t
  where
    ss' = if isFreePredInType p t then (ss ++ s) else s

substPredP _  (PMono _ _)       
  = error $ "PMono found in substPredP"

splitPVar :: PVar r -> RReft -> (RReft, [PVar ()])
splitPVar pv (U x (Pr pvs)) = (U x (Pr pvs'), epvs)
  where
    (epvs, pvs') = partition (uPVar pv ==) pvs

isFreePredInType :: PVar Type -> RefType -> Bool
isFreePredInType π (TApp _ ts _ r)
  = any (isFreePredInType π) ts || isPredInURef π r
isFreePredInType π (TVar _ r)
  = isPredInURef π r
isFreePredInType π (TFun xts xt hi ho r)
  = isPredInURef π r || any (isFreePredInType π) (b_type <$> bs)
  where bs = xt : xts ++ heapTypes hi ++ heapTypes ho
isFreePredInType π (TObj xts r)
  = any (isFreePredInType π) (b_type <$> xts) || isPredInURef π r
isFreePredInType _ (TBd _)
  = False
isFreePredInType π (TAll _ t)
  = isFreePredInType π t
isFreePredInType π (TAllP π' t)
  = (π /= π') && isFreePredInType π t

isPredInURef π (U _ (Pr πs)) = any (uPVar π ==) πs    

meetListWithPSubs πs ss r1 r2    = foldl' (meetListWithPSub ss r1) r2 πs
meetListWithPSubsRef πs ss r1 r2 = foldl' ((meetListWithPSubRef ss) r1) r2 πs

-- meetListWithPSub ::  (Reftable r, PPrint t) => [(Symbol, RSort)]-> r -> r -> PVar t -> r
meetListWithPSub ss r1 r2 π
  | all (\(_, x, y) -> EVar x == y) (pv_as π)
  = r2 `meet` r1
  | all (\(_, x, y) -> EVar x /= y) (pv_as π)
  = r2 `meet` (subst su r1)
  | otherwise
  = errorstar $ "meetListWithPSub partial application" ++ ppshow π
  where su  = mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> ss) (pv_as π)]

meetListWithPSubRef ss (PPoly s1 r1) (PPoly s2 r2) π
  | all (\(_, x, EVar y) -> x == y) (pv_as π)
  = PPoly s1 $ r2 `meet` r1      
  | all (\(_, x, EVar y) -> x /= y) (pv_as π)
  = PPoly s2 $ r2 `meet` (subst su r1)
  | otherwise
  = errorstar $ "PredType.meetListWithPSubRef partial application to " ++ ppshow π
  where su  = mkSubst [(x, y) | (x, (_, _, y)) <- zip (fst <$> s1) (pv_as π)]

uPVar = fmap (const ())                   
-------------------------------------------------------------------------------
-----------------------------  Predicate Application --------------------------
-------------------------------------------------------------------------------
pappArity  = 2
pappSym n  = dummyLoc (S $ "papp" ++ show n)

pappSort n = RR (FFunc n $ args ++ [bSort]) top
  where args  = FVar <$> [0..n]
        bSort = FApp boolFTyCon []

pVartoRConc p (v, args)
  = RConc $ pApp (pv_sym p) $ EVar v:(thd3 <$> args)

pappSymSorts = [ (F.val $ pappSym n, pappSort n) | n <- [1..pappArity] ]

pApp :: Symbol -> [Expr] -> Pred
pApp p es= PBexp $ EApp (pappSym $ length es) (EVar p:es)

toPredType :: (Reftable r1, Reftable r2) => PVar (RType r1) -> RType r2
toPredType π = TApp (TDef (Id dummySpan "Pred")) (fmap (const top) <$> ts) [] top
  where ts = pv_ty π : (fst3 <$> pv_as π)

