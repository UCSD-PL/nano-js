-- | Global type definitions for Refinement Type Checker

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE NoMonomorphismRestriction   #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Nano.Typecheck.Types (

  -- * Programs
    Nano (..)
  , NanoBare
  , NanoSSA
  , NanoType
  , Source (..)
  , FunctionStatement
  , mapCode
  -- , sourceNano
  -- , sigsNano

  -- * (Refinement) Types
  , RHeap    -- l |-> T
  , RHeapEnv -- l |-> x:T
  , RType (..)
  , UReft (..)
  , UReftable (..)
  , Predicate (..)
  , Bind (..)
  , Measure
  , TDefId
  , toType
  , ofType
  , strengthen 
  , strengthenContainers 
  , updateField

  -- * Manipulating RefType
  , rTypeReft
  , rTypeSort
  , refSort, recSort, tdefSort
  , rTypeSortedReft
  , rTypeValueVar

  -- * Traversing types
  , efoldReft, foldReft
  , emapReft
  , mapTys
  , mapBind 
  -- * Helpful checks
  , isTop, isNull, isUndefined, isObj, isUnion

  -- * Constructing Types
  , mkUnion, mkUnionR, mkUnionRef

  -- * Deconstructing Types
  , bkFun
  , funHeaps
  , bkAll
  , bkUnion, rUnion, rsUnion, rTypeR, setRTypeR
  , noUnion, unionCheck
  , typeVarArgs
  , typeRefArgs

  -- * Regular Types
  , Type
  , BHeap
  , TBody (..)
  , TVar (..)
  , PVar (..)
  , PRef (..)
  , Ref
  , TCon (..)

  -- * Primitive Types
  , tInt
  , tBool
  , tString
  , tTop
  , tVoid
  , tErr
  , tFunErr
  , tVar
  , tUndef
  , tNull
  , tRef

  -- * Nil
  , nilLoc
  , nilBind

  -- * Operator Types
  , infixOpTy
  , prefixOpTy 
  
  -- * Annotations
  , Annot (..)
  , Fact
  , Fact_ (..)
  , AnnBare_ ,AnnBare
  , AnnSSA_, AnnSSA
  , AnnType_, AnnType
  , AnnInfo_, AnnInfo
  , isAsm
    
  , restrictHeap  
  , locs
  , locsNil
  , deleteLocsTy
  ) where 

import           Text.Printf
import           Data.Hashable
import           Data.Maybe                     (fromMaybe, catMaybes)
import           Data.Monoid                    hiding ((<>))            
import qualified Data.List                      as L
import qualified Data.HashMap.Strict            as M
import           Data.Generics                   
import           Data.Typeable                  ()
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser    (SourceSpan (..))
import           Language.Nano.Types
import           Language.Nano.Errors
import           Language.Nano.Env
import           Language.Nano.Typecheck.Heaps

-- import           Language.Fixpoint.Names (propConName)
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Misc
import           Language.Fixpoint.PrettyPrint
import           Text.PrettyPrint.HughesPJ 

import           Control.Applicative            hiding (empty)
import           Control.Monad.Error            ()

-- import           Debug.Trace (trace)

-- | Type Variables
data TVar = TV { tv_sym :: F.Symbol
               , tv_loc :: SourceSpan 
               }
            deriving (Show, Ord, Data, Typeable)

instance Eq TVar where 
  a == b = tv_sym a == tv_sym b

instance IsLocated TVar where 
  srcPos = tv_loc

instance Hashable TVar where 
  hashWithSalt i α = hashWithSalt i $ tv_sym α 

instance F.Symbolic TVar where
  symbol = tv_sym 

instance PP TVar where 
  pp     = pprint . F.symbol

-- | Abstract Predicate Variables (number<p>)
data PVar t = PV { pv_sym :: !F.Symbol
                 , pv_loc :: !SourceSpan
                 , pv_ty  :: !t
                 , pv_as  :: ![(t, F.Symbol, F.Expr)]
                 }
            deriving (Show, Data, Typeable)

data PRef t s m = PMono [(F.Symbol, t)] s
                | PPoly [(F.Symbol, t)] m
                  deriving (Eq, Ord, Show, Functor, Data, Typeable)

type Ref r = PRef Type r (RType r)

instance Eq (PVar a) where
  a == b = pv_sym a == pv_sym b
    
instance Ord (PVar a) where
  compare (PV n _ _ _) (PV n' _ _ _) = compare n n'

instance Functor PVar where
  fmap f (PV n l t txys) = PV n l (f t) (mapFst3 f <$> txys)

instance F.Symbolic (PVar a) where
  symbol = pv_sym

instance F.Symbolic a => F.Symbolic (Located a) where 
  symbol = F.symbol . val
    

-- | Constructed Type Bodies
data TBody r 
   = TD { td_con  :: !TCon          -- TDef name ...
        , td_self :: F.Symbol       -- "Self" binder for body
        , td_args :: ![TVar]        -- Type variables
        , td_refs :: ![PVar Type]   -- Predicate Refinements
        , td_heap :: !(RHeapEnv r)  -- An existentially quantified heap
        , td_body :: !(RType r)     -- int or bool or fun or object ...
        , td_pos  :: !SourceSpan    -- Source position
        } deriving (Eq, Ord, Show, Functor, Data, Typeable)

type Measure = (F.Symbol, [F.Symbol], F.Expr) -- (name, v in keys(v) = ..., e)

typeRefArgs γ t@(TDef i) =
  case envFindTy i γ of
    Just (TBd body) -> td_refs body
    _               -> [] -- error $ "BUG: typeRefArgs of " ++ ppshow t
typeRefArgs _ _        = []

typeVarArgs γ t@(TDef i) =                          
  case envFindTy i γ of
    Just (TBd body) -> td_args body
    _               -> error $ "BUG: typeVarArgs of " ++ ppshow t

typeVarArgs _ _        = []

-- | Type Constructors
data TCon 
  = TInt                   
  | TBool                
  | TString
  | TVoid             
  | TTop
  | TRef Location
  | TDef TDefId
  | TUn
  | TNull
  | TUndef
    deriving (Show, Ord, Data, Typeable)

type TDefId = Id SourceSpan

type RHeap r = Heap (RType r)    
type RHeapEnv r = Heap (Bind r)

nilLoc  = "?null"
nilBind = B nilSymbol tUndef

-- | (Raw) Refined Types 
data RType r  
  = TApp  TCon [RType r] [PRef (RType ()) r (RType r)] r
  | TVar  TVar                                         r 
  | TFun  [Bind r] (Bind r) (RHeapEnv r) (RHeapEnv r)  r
  | TObj  [Bind r]                                     r
  | TBd   (TBody r)
  | TAll  TVar (RType r)
  | TAllP (PVar (RType ())) (RType r)
    deriving (Ord, Show, Data, Typeable)

instance Functor RType where
  fmap f = emapReft (\_ -> f) []

mapTys f (TAll v t)            = TAll v  $ mapTys f t           
mapTys f (TAllP v t)           = TAllP v $ mapTys f t
mapTys f (TApp c ts rs r)      = f $ TApp c (mapTys f <$> ts) rs r
mapTys f (TFun xts xt hi ho r) = TFun (g <$> xts) (g $ xt) (g <$> hi) (g <$> ho) r
  where g = mapBind (mapTys f)
mapTys f (TObj xts r)          = TObj (mapBind f <$> xts) r
mapTys f t                     = f t

mapBind f (B x t) = B x $ f t

-- Lifted from LiquidHaskell             
type UsedPVar      = PVar ()
newtype Predicate  = Pr [UsedPVar] deriving (Data, Typeable, Eq, Show, Ord) 

instance Monoid Predicate where
  mempty       = pdTrue
  mappend p p' = pdAnd [p, p']

instance (Monoid a) => Monoid (UReft a) where
  mempty                    = U mempty mempty
  mappend (U x y) (U x' y') = U (mappend x x') (mappend y y')

pdTrue         = Pr []
pdAnd ps       = Pr (L.nub $ concatMap pvars ps)
pvars (Pr pvs) = pvs

data UReft r
    = U { ur_reft :: !r, ur_pred :: !Predicate }
      deriving (Show, Ord, Eq, Typeable, Data)

class UReftable a r where
  ureft :: a -> UReft r

instance F.Reftable r => UReftable r r where
  ureft r = U r pdTrue

instance F.Reftable r => UReftable Predicate r where
  ureft p = U mempty p

instance F.Reftable r => UReftable (UReft r) r where
  ureft = id

data Bind r
  = B { b_sym  :: F.Symbol
      , b_type :: !(RType r)
      } 
    deriving (Eq, Ord, Show, Functor, Data, Typeable)

instance F.Reftable Predicate where
  isTauto (Pr ps)      = null ps

  bot (Pr _)           = errorstar "No BOT instance for Predicate"
  ppTy r d | F.isTauto r          = d 
           -- | not (F.ppPs F.ppEnv) = d
           | otherwise            = d <> (angleBrackets $ pp r)
  
  toReft               = errorstar "TODO: instance of toReft for Predicate"
  params               = errorstar "TODO: instance of params for Predicate"

instance (PP r, F.Reftable r) => F.Reftable (UReft r) where
  isTauto            = isTauto_ureft 
  -- ppTy (U r p) d     = ppTy r (ppTy p d) 
  ppTy               = ppTy_ureft
  toReft (U r _)     = F.toReft r
  params (U r _)     = F.params r
  bot (U r _)        = U (F.bot r) (Pr [])

isTauto_ureft u      = F.isTauto (ur_reft u) && F.isTauto (ur_pred u)

ppTy_ureft u@(U r p) d 
  | isTauto_ureft u  = d
  | otherwise        = ppr_reft r (F.ppTy p d)

ppr_reft r d         = braces (F.toFix v <+> colon <+> d <+> text "|" <+> pprint r')
  where 
    r'@(F.Reft (v, _)) = F.toReft r

------------------------------------------------------------------------------------------
-- | Substitutions -----------------------------------------------------------------------
------------------------------------------------------------------------------------------
instance F.Subable Predicate where
  syms (Pr pvs)     = concatMap F.syms pvs 
  subst s (Pr pvs)  = Pr (F.subst s <$> pvs)
  substf f (Pr pvs) = Pr (F.substf f <$> pvs)
  substa f (Pr pvs) = Pr (F.substa f <$> pvs)

instance F.Subable r => F.Subable (UReft r) where
  syms (U r p)     = F.syms r ++ F.syms p 
  subst s (U r z)  = U (F.subst s r)  (F.subst s z)
  substf f (U r z) = U (F.substf f r) (F.substf f z) 
  substa f (U r z) = U (F.substa f r) (F.substa f z) 
 
instance (F.Reftable r {-, F.RefTypable p c tv r -})
    => F.Subable (PRef Type r (RType r)) where
  syms (PMono ss r)     = (fst <$> ss) ++ F.syms r
  syms (PPoly ss r)     = (fst <$> ss) ++ F.syms r
  subst su (PMono ss r) = PMono ss (F.subst su r)
  subst su (PPoly ss t) = PPoly ss (F.subst su <$> t)
  substf f (PMono ss r) = PMono ss (F.substf f r) 
  substf f (PPoly ss t) = PPoly ss (F.substf f <$> t)
  substa f (PMono ss r) = PMono ss (F.substa f r) 
  substa f (PPoly ss t) = PPoly ss (F.substa f <$> t)

instance F.Subable UsedPVar where 
  syms pv         = [ y | (_, x, F.EVar y) <- pv_as pv, x /= y ]
  subst s pv      = pv { pv_as = mapThd3 (F.subst s)  <$> pv_as pv }  
  substf f pv     = pv { pv_as = mapThd3 (F.substf f) <$> pv_as pv }  
  substa f pv     = pv { pv_as = mapThd3 (F.substa f) <$> pv_as pv }  

instance (F.Reftable r, F.Subable r) => F.Subable (RType r) where
  syms        = foldReft (\r acc -> F.syms r ++ acc) [] 
  substa      = fmap . F.substa 
  substf f    = emapReft (F.substf . F.substfExcept f) [] 
  subst su    = emapReft (F.subst  . F.substExcept su) []
  subst1 t su = emapReft (\xs r -> F.subst1Except xs r su) [] t

instance (F.Reftable r, F.Subable r) => F.Subable (RHeap r) where
  syms        = concatMap F.syms . heapTypes
  substa      = fmap . F.substa
  substf f    = fmap (F.substf f)
  subst su    = fmap (F.subst su)

------------------------------------------------------------------------------------------
-- | Traversals over @RType@ -------------------------------------------------------------
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
emapReft  :: ([F.Symbol] -> a -> b) -> [F.Symbol] -> RType a -> RType b
------------------------------------------------------------------------------------------
emapReft f γ (TVar α r)          = TVar α (f γ r)
emapReft f γ (TApp c ts ps r)    = TApp c (emapReft f γ <$> ts) (emapRef f γ <$> ps) (f γ r)
emapReft f γ (TAll α t)          = TAll α (emapReft f γ t)
emapReft f γ (TAllP π t)         = TAllP π (emapReft f γ t)
emapReft f γ (TFun xts t hi ho r)= TFun (emapReftBind f γ' <$> xts)
                                        (emapReftBind f γ' t) hi' ho' (f γ r) 
  where 
    γ'                           = (b_sym <$> xts) ++ γ 
    hi'                          = fmap (emapReftBind f γ) hi
    ho'                          = fmap (emapReftBind f γ) ho
    -- ts                           = b_type <$> xts 
emapReft f γ (TObj bs r)         = TObj (emapReftBind f γ' <$> bs) (f γ r)
  where 
    γ'                           = (b_sym <$> bs) ++ γ 
emapReft f γ t@(TBd bd)          = TBd $ emapReftBody f γ bd
emapReft _ _ t                   = error "Not supported in emapReft"

emapRef f γ (PMono xs r)         = PMono xs (f γ r)                                   
emapRef f γ (PPoly xs t)         = PPoly xs (emapReft f γ t)

emapReftBind f γ (B x t)         = B x $ emapReft f γ t

emapReftBody f γ bd
  = bd { td_heap = fmap (emapReftBind f γ) $ td_heap bd
       , td_body = emapReft f γ            $ td_body bd
       } 

------------------------------------------------------------------------------------------
-- | fold over @RType@ -------------------------------------------------------------------
------------------------------------------------------------------------------------------

------------------------------------------------------------------------------------------
foldReft  :: (F.Reftable r) => (r -> a -> a) -> a -> RType r -> a
------------------------------------------------------------------------------------------
foldReft  f = efoldReft (\_ -> ()) (\_ -> f) F.emptySEnv 

------------------------------------------------------------------------------------------
efoldReft :: (F.Reftable r) => (RType r -> b) -> (F.SEnv b -> r -> a -> a) -> F.SEnv b -> a -> RType r -> a
------------------------------------------------------------------------------------------
efoldReft _ f γ z (TVar _ r)          = f γ r z
efoldReft g f γ z t@(TApp _ ts ps r)  = f γ r $ efoldRefts g f (efoldExt g (B (rTypeValueVar t) t) γ) z ts
    where
      z'                              = L.foldl' (efoldRef g f γ) z ps
efoldReft g f γ z (TAll _ t)          = efoldReft g f γ z t
efoldReft g f γ z (TAllP _ t)         = efoldReft g f γ z t
efoldReft g f γ z (TFun xts t h h' r) = f γ r $ efoldRefts g f γ' z ts
  where 
    γ'                                = foldr (efoldExt g) γ (t:xts)
    ts                                = (b_type <$> (t:xts))
                                     ++ heapTypes (b_type <$> h)
                                     ++ heapTypes (b_type <$> h')
efoldReft g f γ z (TObj xts r)        = f γ r $ (efoldRefts g f γ' z (b_type <$> xts))
  where 
    γ'                                = foldr (efoldExt g) γ xts
efoldReft _ _ _ _ _                   = error "Not supported in efoldReft"

efoldRefts g f γ z ts                 = L.foldl' (efoldReft g f γ) z ts

efoldExt g xt γ                       = F.insertSEnv (b_sym xt) (g $ b_type xt) γ

goPred' g xs γ                  = L.foldl' (\γ (x,t) -> F.insertSEnv x (g $ ofType t) γ) γ  xs

efoldRef  g f γ z (PMono xs r)  = f γ' r z
    where γ' = L.foldl' (\γ (x,t) -> F.insertSEnv x (g $ ofType t) γ) γ xs
efoldRef  g f γ z (PPoly xs t)  = efoldReft g f γ' z t
    where γ' = L.foldl' (\γ (x,t) -> F.insertSEnv x (g $ ofType t) γ) γ xs

------------------------------------------------------------------------------
-- | Converting RType to Fixpoint --------------------------------------------
------------------------------------------------------------------------------

rTypeSortedReft   ::  (F.Reftable r) => RType r -> F.SortedReft
rTypeSortedReft t = F.RR (rTypeSort t) (rTypeReft t)

rTypeReft         :: (F.Reftable r) => RType r -> F.Reft
rTypeReft         = fromMaybe mempty . fmap F.toReft . stripRTypeBase 

rTypeValueVar     :: (F.Reftable r) => RType r -> F.Symbol
rTypeValueVar t   = vv where F.Reft (vv,_) =  rTypeReft t 

------------------------------------------------------------------------------------------
rTypeSort :: (F.Reftable r) => RType r -> F.Sort
------------------------------------------------------------------------------------------

rTypeSort (TApp TInt [] _ _)   = F.FInt
rTypeSort (TVar α _)           = F.FObj $ F.symbol α 
rTypeSort t@(TAll _ _)         = rTypeSortForAll t 
rTypeSort t@(TAllP _ _)        = rTypeSortForAll t 
rTypeSort (TFun xts t _ _ _)   = F.FFunc 0 $ rTypeSort <$> (b_type <$> (xts ++ [t]))
rTypeSort (TApp (TDef (Id _ c)) _ _ _)
  | c /= "set" = tdefSort
rTypeSort (TApp TUn ts _ _)    
  | length (L.nub (toType <$> ts)) == 1 = rTypeSort (head ts)
  | rTypePtrUnion ts           = refSort
rTypeSort (TApp c ts _ _)      = rTypeSortApp c ts 
rTypeSort (TObj _ _)           = recSort
rTypeSort t                    = error ("Type: " ++ ppshow t ++ 
                                    " is not supported in rTypeSort")

refSort = F.FApp (rawStringFTycon "Ref") []
recSort = F.FApp (rawStringFTycon "Rec") []
tdefSort = F.FApp (rawStringFTycon "T") []

rTypePtrUnion ts = all isPtr ts
  where
   isPtr (TApp TNull _ _ _)    = True
   isPtr (TApp (TRef _) _ _ _) = True
   isPtr _                     = False                          

rTypeSortApp TInt [] = F.FInt
rTypeSortApp TUn  _  = F.FApp (tconFTycon TUn) [] -- simplifying union sorts, the checks will have been done earlier
rTypeSortApp c ts    = F.FApp (tconFTycon c) (rTypeSort <$> ts) 

tconFTycon TInt      = F.intFTyCon
tconFTycon TBool     = rawStringFTycon "boolean"
tconFTycon TVoid     = rawStringFTycon "void"
tconFTycon (TDef s)  = F.stringFTycon $ F.Loc (sourcePos s) (unId s)
tconFTycon TUn       = F.intFTyCon -- rawStringFTycon "union"
tconFTycon TString   = F.strFTyCon -- F.stringFTycon "string"
tconFTycon TTop      = rawStringFTycon "top"
tconFTycon TNull     = rawStringFTycon "Ref"
tconFTycon TUndef    = F.intFTyCon
tconFTycon (TRef l)  = rawStringFTycon "Ref"


rTypeSortForAll t    = genSort n θ $ rTypeSort tbody
  where 
    (αs, πs, tbody)  = bkAll t
    n                = length αs
    θ                = M.fromList $ zip (F.symbol <$> αs) (F.FVar <$> [0..])
    
genSort n θ (F.FFunc _ t)  = F.FFunc n (F.sortSubst θ <$> t)
genSort n θ t              = F.FFunc n [F.sortSubst θ t]

------------------------------------------------------------------------------------------
stripRTypeBase :: RType r -> Maybe r 
------------------------------------------------------------------------------------------
stripRTypeBase (TApp _ _ _ r)   = Just r
stripRTypeBase (TVar _ r)       = Just r
stripRTypeBase (TFun _ _ _ _ r) = Just r
stripRTypeBase (TObj _ r)       = Just r
stripRTypeBase _                = Nothing
 

-- | Standard Types
type Type    = RType ()
type BHeap   = RHeap ()

-- | Stripping out Refinements 
toType :: RType a -> Type
toType = toTypePreds . fmap (const ())

toTypePreds (TApp c ts rs r) = TApp c ts rs' r
  where rs' = toTypeRef <$> rs
toTypePreds t                = t
                               
toTypeRef (PMono ss s) = PMono ss ()
toTypeRef (PPoly ss t) = PPoly ss (toType t)
  
-- | Adding in Refinements
ofType :: (F.Reftable r) => Type -> RType r
ofType = fmap (const mempty)

locs :: RType r -> [Location]
locs = locs' locsNonNil'

locsNil :: RType r -> [Location]
locsNil = locs' locsNil'

locs' f t             = L.nub (go t)
  where
    go (TApp c ts _ _) = f c ++ (concatMap go ts)
    go (TObj bs _)   = concatMap (go . b_type) bs
    go _             = []

locsNonNil' :: TCon -> [Location]
locsNonNil' (TRef l) = [l]
locsNonNil' _        = []

locsNil' :: TCon -> [Location]
locsNil' (TRef l) = [l]
locsNil' TNull    = [nilLoc]
locsNil' _        = []


-- | RHeap utils
---------------------------------------------------------------------------------
deleteLocsTy :: (F.Reftable r, Ord r, PP r) => [Location] -> RType r -> RType r                 
---------------------------------------------------------------------------------
deleteLocsTy = foldl (\f l -> (deleteLocTy l . f)) id

deleteLocTy l (TObj bs r) = TObj bs' r
  where
    bs' = map filterLoc bs
    filterLoc (B i t) = B i $ deleteLocTy l t

deleteLocTy l   (TApp TUn ts rs r) = case ts' of
                                      [] -> err
                                      _  -> mkUnionR rs r ts'
  where
    ts' = catMaybes $ map (filterLoc l . deleteLocTy l) ts
    err = errorstar "deleteLocTy: Empty type"

deleteLocTy l t@(TApp _ [] _ _) = t
deleteLocTy l   (TApp c ts ps r) = case ts' of
                                     [] -> err
                                     _  -> TApp c ts' ps r
  where 
    ts' = catMaybes $ map (filterLoc l . deleteLocTy l) ts
    err = errorstar "deleteLocTy: Empty type"
    
deleteLocTy _ t               = t      

filterLoc l (TApp (TRef l') _ _ _) | l == l' = Nothing
filterLoc l t                              = Just t

heapEnvToHeap :: RHeapEnv r -> RHeap r
heapEnvToHeap h = b_type <$> h
                 
---------------------------------------------------------------------------------
restrictHeap :: (F.Reftable r) => [Location] -> RHeap r -> RHeap r
---------------------------------------------------------------------------------
restrictHeap [] _ = heapEmpty
restrictHeap ls h = heapCombineWith const [h1, h2]
  where
    h1       = restrictHeap ls' (heapFromBinds "restrictHeap h1" nbs)
    h2       = heapFromBinds "restrictHeap h2" bs
    (bs,nbs) = L.partition ((`elem` ls) . fst) $ heapBinds h
    ls'      = concatMap (filter (not . (`elem` ls)) . locs . snd) bs

bkFun :: RType r -> Maybe ([TVar], [PVar Type], [Bind r], RHeapEnv r, RHeapEnv r, Bind r)
bkFun t = do let (αs, πs, t')   = bkAll t
             (xts, t'', h, h')  <- bkArr t'
             return (αs, πs, xts, h, h', t'')

bkArr (TFun xts t h h' _) = Just (xts, t, h, h')
bkArr _                   = Nothing

bkAll                :: RType a -> ([TVar], [PVar Type], RType a)
bkAll t              = go [] [] t
  where 
    go αs πs (TAll α t)  = go (α : αs) πs t
    go αs πs (TAllP π t) = go αs (π : πs) t
    go αs πs t           = (reverse αs, reverse πs, t)

funHeaps :: RType r -> Maybe (RHeapEnv r, RHeapEnv r)
funHeaps = (stripHeaps =<<) . bkFun
  where
    stripHeaps (_,_,_,σ,σ',_) = return (σ,σ')
---------------------------------------------------------------------------------
updateField :: (Ord r, Eq r, F.Reftable r) =>
  RType r -> F.Symbol -> RType r -> RType r
---------------------------------------------------------------------------------
updateField t f (TObj bs r) = TObj (scanUpdate bs) r
  where scanUpdate []     = [B f t]
        scanUpdate (b:bs) = if b_sym b == f then
                              (B (b_sym b) t):bs
                            else
                              b:scanUpdate bs

updateField t' f t =
  errorstar $ (printf "Can not update %s.%s = %s" (ppshow t) (ppshow f) (ppshow t'))


---------------------------------------------------------------------------------
mkUnion :: (Ord r, Eq r, F.Reftable r) => [RType r] -> RType r
---------------------------------------------------------------------------------
mkUnion = mkUnionRef mempty

---------------------------------------------------------------------------------
mkUnionRef :: (Ord r, Eq r, F.Reftable r) => r -> [RType r] -> RType r
---------------------------------------------------------------------------------
mkUnionRef = mkUnionR []

---------------------------------------------------------------------------------
mkUnionR :: (Ord r, Eq r, F.Reftable r) => [PRef Type r (RType r)] -> r -> [RType r] -> RType r
---------------------------------------------------------------------------------
mkUnionR rs _ [ ] = tErr
mkUnionR rs r [t] = strengthen t r
mkUnionR rs r ts  | length ts' > 1 = TApp TUn ts' rs r
               | otherwise      = strengthen (head ts') r
  where ts'  = L.sort $ L.nub ts

               
---------------------------------------------------------------------------------
bkUnion :: RType r -> [RType r]
---------------------------------------------------------------------------------
bkUnion (TApp TUn xs _ _) = xs
bkUnion t               = [t]

-- | Strengthen the top-level refinement
---------------------------------------------------------------------------------
strengthen                   :: F.Reftable r => RType r -> r -> RType r
---------------------------------------------------------------------------------
{-strengthen t = setRTypeR t . (rTypeR t `F.meet`)-} 
-- The above does not handle cases other than TApp and TVar correctly
strengthen (TApp c ts ps r) r'  = TApp c ts ps $ r' `F.meet` r 
strengthen (TVar α r)       r'  = TVar α    $ r' `F.meet` r 
strengthen t _                   = t                         

-- NOTE: r' is the OLD refinement. 
--       We want to preserve its VV binder as it "escapes", 
--       e.g. function types. Sigh. Should have used a separate function binder.


-- | Strengthen the refinement of a type @t2@ deeply, using the 
-- refinements of an equivalnet (having the same raw version) 
-- type @t1@
-- TODO: Add checks for equivalence in union and objects
strengthenContainers (TApp TUn ts ps r) (TApp TUn ts' ps' r') =
  TApp TUn (zipWith strengthenContainers ts ts') pm rm
  where
    rm = r' `F.meet` r
    pm = ps' ++ ps

strengthenContainers (TObj ts r) (TObj ts' r') = 
  TObj (zipWith doB ts ts') $ r' `F.meet` r
  where 
    doB (B s t) (B s' t') | s == s' =  B s $ strengthenContainers t t'
    doB _       _                   = errorstar "strengthenContainers: sanity check - 1"
strengthenContainers t t' | toType t == toType t' = strengthen t' $ rTypeR t
strengthenContainers _ _  | otherwise = errorstar "strengthenContainers: sanity check - 2"

instance (F.Reftable r) => Monoid (RType r) where
  mempty  = error "mempty RType"
  mappend = strengthenContainers

instance (F.Reftable r) => F.Reftable (RType r) where
  isTauto = isTrivial
  ppTy    = error "ppTy RPoly Reftable" 
  toReft  = error "toReft on RType"
  params  = error "params on RType"
  bot     = error "bot on RType"

instance (PP r, F.Reftable r)
   => Monoid (PRef Type r (RType (UReft r))) where
  mempty = PMono [] mempty
  mappend (PMono s1 r1) (PMono s2 r2) = PMono (s1 ++ s2) $ r1 `F.meet` r2
  mappend (PMono s1 r) (PPoly s2 t)   = PPoly (s1 ++ s2) $ t `strengthen` (U r pdTrue)
  mappend (PPoly s1 t) (PMono s2 r)   = PPoly (s1 ++ s2) $ t  `strengthen` (U r pdTrue)
  mappend (PPoly s1 t1) (PPoly s2 t2) = PPoly (s1 ++ s2) $ t1 `strengthenContainers` t2

instance (PP r, F.Reftable r)
   => Monoid (PRef Type r (RType r)) where
  mempty = PMono [] mempty
  mappend (PMono s1 r1) (PMono s2 r2) = PMono (s1 ++ s2) $ mappend r1 r2
  mappend (PMono s1 r) (PPoly s2 t)   = PPoly (s1 ++ s2) $ t `strengthen` r
  mappend (PPoly s1 t) (PMono s2 r)   = PPoly (s1 ++ s2) $ t  `strengthen` r
  mappend (PPoly s1 t1) (PPoly s2 t2) = PPoly (s1 ++ s2) $ t1 `strengthenContainers` t2

instance (PP r, F.Reftable r) => F.Reftable (Ref r) where
  isTauto (PMono _ r) = F.isTauto r
  isTauto (PPoly _ t) = isTrivial t
  ppTy (PMono _ r) d  = F.ppTy r d
  ppTy (PPoly _ _) _  = errorstar "RefType: Reftable ppTy in RPoly"
  toReft              = errorstar "RefType: Reftable toReft"
  params              = errorstar "RefType: Reftable params for Ref"
  bot                 = errorstar "RefType: Reftable bot    for Ref"
  
  
isTrivial t = foldReft (\r b -> F.isTauto r && b) True t

---------------------------------------------------------------------------------
-- | Helpful type checks
---------------------------------------------------------------------------------

-- | Top-level Top (any) check
isTop :: RType r -> Bool
isTop (TApp TTop _ _ _)   = True 
isTop (TApp TUn  ts _ _)  = any isTop ts
isTop _                   = False

isUndefined :: RType r -> Bool
isUndefined (TApp TUndef _ _ _) = True 
isUndefined _                   = False

isNull :: RType r -> Bool
isNull (TApp TNull _ _ _) = True 
isNull _                  = False

isObj :: RType r -> Bool
isObj (TObj _ _)        = True
isObj _                 = False

isUnion :: RType r -> Bool
isUnion (TApp TUn _ _ _) = True           -- top-level union
isUnion _                = False

-- Get the top-level refinement for unions - use Top (True) otherwise
-- TODO: Fill up for other types
rUnion               :: F.Reftable r => RType r -> r
rUnion (TApp TUn _ _ r) = r
rUnion _                = mempty

rsUnion               :: F.Reftable r => RType r -> [Ref r]
rsUnion (TApp TUn _ r _) = r
rsUnion _                = []
 
-- Get the top-level refinement 
rTypeR :: RType r -> r
rTypeR (TApp _ _ _ r)   = r
rTypeR (TVar _ r)       = r
rTypeR (TFun _ _ _ _ r) = r
rTypeR (TObj _ r)       = r
rTypeR (TBd  _)         = errorstar "Unimplemented: rTypeR - TBd"
rTypeR (TAll _ _ )      = errorstar "Unimplemented: rTypeR - TAll"
rTypeR (TAllP _ _ )     = errorstar "Unimplemented: rTypeR - TAllP"

setRTypeR :: RType r -> r -> RType r
setRTypeR (TApp c ts ps _) r' = TApp c ts ps r'
setRTypeR (TVar v _)    r'   = TVar v r'
setRTypeR (TFun xts ot ih oh _) r' = TFun xts ot ih oh r'
setRTypeR (TObj xts _)  r'   = TObj xts r'
setRTypeR (TBd  _)     _     = errorstar "Unimplemented: setRTypeR - TBd"
setRTypeR (TAll _ _ )  _     = errorstar "Unimplemented: setRTypeR - TAll"
setRTypeR (TAllP _ _ ) _     = errorstar "Unimplemented: setRTypeR - TAllP"


---------------------------------------------------------------------------------------
noUnion :: (F.Reftable r) => RType r -> Bool
---------------------------------------------------------------------------------------
noUnion (TApp TUn _ _ _)    = False
noUnion (TApp _  rs _ _)    = and $ map noUnion rs
noUnion (TFun bs rt h h' _) = and $ map noUnion $ ((map b_type (rt:bs))
                                                 ++ heapTypes (b_type <$> h)
                                                 ++ heapTypes (b_type <$> h'))
noUnion (TObj bs    _)      = and $ map noUnion $ map b_type bs 
noUnion (TBd  _      )      = error "noUnion: cannot have TBodies here"
noUnion (TAll _ t    )      = noUnion t
noUnion (TAllP _ t   )      = noUnion t
noUnion _                   = True

unionCheck t | noUnion t = t 
unionCheck t | otherwise = error $ printf "%s found. Cannot have unions." $ ppshow t


instance Eq TCon where
  TInt    == TInt    = True   
  TBool   == TBool   = True           
  TString == TString = True
  TVoid   == TVoid   = True         
  TTop    == TTop    = True
  TDef i1 == TDef i2 = F.symbol i1 == F.symbol i2
  TRef l1 == TRef l2 = l1 == l2
  TUn     == TUn     = True
  TNull   == TNull   = True
  TUndef  == TUndef  = True
  _       == _       = False
 
instance (Eq r, Ord r, F.Reftable r) => Eq (RType r) where
  TApp TUn t1 _ _        == TApp TUn t2 _ _       = (null $ t1 L.\\ t2) && (null $ t2 L.\\ t1)
    {-tracePP (printf "Diff: %s \\ %s" (ppshow $ L.nub t1) (ppshow $ L.nub t2)) $-}
  TApp c1 t1s ps1 r1     == TApp c2 t2s ps2 r2    = (c1, t1s, ps1, r1) == (c2, t2s, ps2, r2)
  TVar v1 r1             == TVar v2 r2            = (v1, r1)       == (v2, r2)
  TFun b1 t1 hi1 ho1 r1  == TFun b2 t2 hi2 ho2 r2 = (b1, t1, hi1, ho1, r1) == (b2, t2, hi2, ho2, r2)
  TObj b1 r1             == TObj b2 r2            = (null $ b1 L.\\ b2) && (null $ b2 L.\\ b1) && r1 == r2
  TBd b1                 == TBd b2                = b1 `eqTBd` b2
  TAll _ _               == TAll  _ _             = undefined -- TODO
  TAllP _ _              == TAllP _ _             = undefined -- TODO
  _                      == _                     = False

eqTBd (TD c1 v1 a1 r1 h1 b1 _) (TD c2 v2 a2 r2 h2 b2 _)
  = (c1, v1, a1, r1, h1, b1) == (c2, v2, a2, r2, h2, b2)


---------------------------------------------------------------------------------
-- | Nano Program = Code + Types for all function binders
---------------------------------------------------------------------------------

data Nano a t =
    Nano { code   :: !(Source a)                     -- ^ Code to check
         , specs  :: !(Env t)                        -- ^ Imported Specifications
         , defs   :: !(Env t)                        -- ^ Signatures for Code
         , consts :: !(Env t)                        -- ^ Measure Signatures 
         , tDefs  :: !(Env t)                        -- ^ Type definitions
         , tMeas  :: !(M.HashMap F.Symbol Measure)   -- ^ Measure implementations
         , tRMeas :: !(M.HashMap F.Symbol [Measure]) -- ^ Type (recursive) measure definitions
         , quals  :: ![F.Qualifier]                  -- ^ Qualifiers
         , invts  :: ![Located t]                    -- ^ Type Invariants
         } deriving (Functor, Data, Typeable)

type NanoBareR r   = Nano (AnnBare_ r) (RType r)
type NanoSSAR r    = Nano (AnnSSA_  r) (RType r)
type NanoTypeR r   = Nano (AnnType_ r) (RType r)

type NanoBare   = NanoBareR ()
type NanoSSA    = NanoSSAR ()
type NanoType   = NanoTypeR ()

{-@ measure isFunctionStatement :: (Statement SourceSpan) -> Prop 
    isFunctionStatement (FunctionStmt {}) = true
    isFunctionStatement (_)               = false
  @-}

{-@ type FunctionStatement = {v:(Statement SourceSpan) | (isFunctionStatement v)} @-}
type FunctionStatement a = Statement a 

{-@ newtype Source a = Src [FunctionStatement a] @-}
-- newtype Source a = Src [FunctionStatement a]
newtype Source a = Src [Statement a]
  deriving (Data, Typeable)

instance Functor Source where 
  fmap f (Src zs) = Src (map (fmap f) zs)

instance PP t => PP (Nano a t) where
  pp pgm@(Nano {code = (Src s) }) 
    =   text "********************** CODE **********************"
    $+$ pp s
    $+$ text "********************** SPECS *********************"
    $+$ pp (specs pgm)
    $+$ text "********************** DEFS *********************"
    $+$ pp (defs  pgm)
    $+$ text "********************** CONSTS ********************"
    $+$ pp (consts pgm) 
    $+$ text "********************** TYPE DEFS *****************"
    $+$ pp (tDefs  pgm)
    $+$ text "********************** MEASURES *************"
    $+$ (vcat . (pp <$>) . M.toList $ tMeas  pgm)
    $+$ text "********************** QUALS *********************"
    $+$ F.toFix (quals  pgm) 
    $+$ text "********************** INVARIANTS ****************"
    $+$ pp (invts pgm) 
    $+$ text "**************************************************"
    
instance Monoid (Nano a t) where 
  mempty        = Nano (Src []) envEmpty envEmpty envEmpty envEmpty M.empty M.empty [] [] 
  mappend p1 p2 = Nano { code   = ss
                       , specs  = e
                       , defs   = e'
                       , consts = cs 
                       , tDefs  = tds
                       , tMeas  = tms
                       , tRMeas = trms
                       , quals  = qs
                       , invts  = is
                       }
    where 
      ss        = Src $ s1 ++ s2
      Src s1    = code p1
      Src s2    = code p2
      e         = envFromList ((envToList $ specs p1) ++ (envToList $ specs p2))
      e'        = envFromList ((envToList $ defs p1)  ++ (envToList $ defs p2))
      cs        = envFromList $ (envToList $ consts p1) ++ (envToList $ consts p2)
      tds       = envFromList $ (envToList $ tDefs p1) ++ (envToList $ tDefs p2)
      tms       = M.fromList $ (M.toList $ tMeas p1) ++ (M.toList $ tMeas p2)
      trms      = M.fromList $ (M.toList $ tRMeas p1) ++ (M.toList $ tRMeas p2)
      qs        = quals p1 ++ quals p2
      is        = invts p1 ++ invts p2

mapCode :: (a -> b) -> Nano a t -> Nano b t
mapCode f n = n { code = fmap f (code n) }

instance PP (F.Symbol, [F.Symbol], F.Expr) where
    pp (m, xs, e) = pp m <+> ppArgs parens comma xs <+> text "=" <+> text (show e)

---------------------------------------------------------------------------
-- | Pretty Printer Instances ---------------------------------------------
---------------------------------------------------------------------------

instance PP () where 
  pp _ = text ""

instance PP a => PP [a] where 
  pp = ppArgs brackets comma 

instance PP a => PP (Maybe a) where 
  pp = maybe (text "Nothing") pp 

instance (PP t) => PP (Heap t) where
  pp h = brackets $ intersperse (text " *") (map ppBind (heapBinds h))
      where ppBind (l, t) = text l <+> text "|->" <+> pp t

instance PP F.Subst where
  pp = text . show

instance PP Predicate where
  pp (Pr [])  = text "true"
  pp (Pr pvs) = hsep $ punctuate (text "&") (map pp pvs)

instance PP r => PP (UReft r) where
  pp (U r p)  = pp r <+> text "U" <+> pp p

instance PP a => PP (PVar a) where
  pp (PV v _ _ as)   = pprint v

instance (F.Reftable a) => PP (PRef Type a (RType a)) where
  pp (PMono [] s) = F.ppTy s $ pprint (F.FVar 0)
  pp (PMono ss s) = text "\\" <+> ppArgs id (text "->") ss <+> text "->" <+> F.ppTy s (pprint (F.FVar 0))

  pp (PPoly [] s) = pp s
  pp (PPoly ss s) = text "\\" <+> ppArgs id (text "->") ss <+> text "->" <+> pp s

-- data PRef t s m = PMono [(F.Symbol, t)] s
--                 | PPoly [(F.Symbol, t)] m

instance F.Reftable r => PP (RType r) where
  pp (TVar α r)                 = F.ppTy r $ pp α 
  pp (TFun xts t h h' _)        = ppArgs parens comma xts
                                  $$ nest 1 (text "/" <+> pp h <+> text "=>")
                                  $$ nest 1 (pp t $$ text "/" <+> pp h')
  pp t@(TAll _ _)               = ppAll $ bkAll t
  pp t@(TAllP _ _)              = ppAll $ bkAll t
  pp (TApp TUn ts ps r)         = F.ppTy r $ parens (ppArgs id (text "+") ts )
  pp (TApp d@(TDef _)ts ps r)   = F.ppTy r $ ppTC d <+> ppArgs brackets comma ts
                                                    <+> ppArgs angleBrackets comma ps
  pp (TApp c [] [] r)           = F.ppTy r $ ppTC c 
  pp (TApp c [] ps r)           = F.ppTy r $ ppTC c <+> ppArgs angleBrackets comma ps
  pp (TApp c ts ps r)           = F.ppTy r $ parens (ppTC c <+> ppArgs id space ts)  
  pp (TObj bs _ )               = ppArgs braces comma bs
  pp (TBd (TD (TDef id) s v πs h r _)) =  pp (F.symbol id)
                                   <+> ppArgs brackets comma v
                                   <+> ppArgs angleBrackets comma πs 
                                   <+> text "∃!" <+> pp h <+> text "."
                                   <+> pp s <+> text ":" <+> pp r
  pp (TBd _)                    = error "This is not an acceptable form for TBody" 

ppAll (αs, πs, t)  = text "forall" <+> ppArgs id space αs <> text " "
                                   <> ppArgs id space πs <> text "."
                                   <+> pp t
instance PP TCon where
  pp TInt             = text "Int"
  pp TBool            = text "Boolean"
  pp TString          = text "String"
  pp TVoid            = text "Void"
  pp TTop             = text "Top"
  pp TUn              = text "Union:"
  pp (TDef x)         = pprint (F.symbol x)
  pp (TRef l)         = text ("<" ++ l ++ ">")
  pp TNull            = text "Null"
  pp TUndef           = text "Undefined"

instance Hashable TCon where
  hashWithSalt s TInt        = hashWithSalt s (0 :: Int)
  hashWithSalt s TBool       = hashWithSalt s (1 :: Int)
  hashWithSalt s TString     = hashWithSalt s (2 :: Int)
  hashWithSalt s TVoid       = hashWithSalt s (3:: Int)
  hashWithSalt s TTop        = hashWithSalt s (4 :: Int)
  hashWithSalt s TUn         = hashWithSalt s (5 :: Int)
  hashWithSalt s TNull       = hashWithSalt s (6 :: Int)
  hashWithSalt s TUndef      = hashWithSalt s (7 :: Int)
  hashWithSalt s (TDef z)    = hashWithSalt s (8 :: Int) + hashWithSalt s (F.symbol z)
  hashWithSalt s (TRef l)    = hashWithSalt s (9 :: Int) + hashWithSalt s l

instance F.Reftable r => PP (Bind r) where 
  pp (B x t)        = pp x <> colon <> pp t 

ppArgs p sep          = p . intersperse sep . map pp
ppTC TInt             = text "Int"
ppTC TBool            = text "Boolean"
ppTC TString          = text "String"
ppTC TVoid            = text "Void"
ppTC TTop             = text "Top"
ppTC TUn              = text "Union:"
ppTC (TRef l)         = text ("<" ++ l ++ ">")
ppTC (TDef x)         = pprint (F.symbol x)
ppTC TNull            = text "Null"
ppTC TUndef           = text "Undefined"


-----------------------------------------------------------------------------
-- | Annotations ------------------------------------------------------------
-----------------------------------------------------------------------------

-- | Annotations: Extra-code decorations needed for Refinement Type Checking
--   Ideally, we'd have "room" for these inside the @Statement@ and
--   @Expression@ type, but are tucking them in using the @a@ parameter.

data Fact_  r
  = PhiVar     !(Id SourceSpan) 
  | FunInst    ![(TVar,RType r)] ![(Location,Location)]
  | WindInst   !Location ![Location] !(Id SourceSpan) ![(TVar,RType r)] ![(Location,Location)]
  | UnwindInst !Location !(Id SourceSpan) ![(Location,Location)]
  | LocInst    !Location
  | WorldInst  ![(Location, Location)]
  | Assume     !(RType r)
  | AssumeH    !(RHeap r)
  | Rename     ![(Location,Location)]
  | Delete     ![Location]
    deriving (Eq, Ord, Show, Data, Typeable)

type Fact = Fact_ ()

data Annot b a = Ann { ann :: a, ann_fact :: [b] } deriving (Show, Data, Typeable)
type AnnBare_ r  = Annot (Fact_ r) SourceSpan -- NO facts
type AnnSSA_  r  = Annot (Fact_ r) SourceSpan -- Only Phi + Assume     facts
type AnnType_ r  = Annot (Fact_ r) SourceSpan -- Only Phi + Typ        facts
type AnnInfo_ r  = M.HashMap SourceSpan [Fact_ r] 

type AnnBare = AnnBare_ () 
type AnnSSA  = AnnSSA_  ()
type AnnType = AnnType_ ()
type AnnInfo = AnnInfo_ ()


instance HasAnnotation (Annot b) where 
  getAnnotation = ann 

instance Ord (AnnSSA_  r) where 
  compare (Ann s1 _) (Ann s2 _) = compare s1 s2

instance Eq (Annot a SourceSpan) where 
  (Ann s1 _) == (Ann s2 _) = s1 == s2

instance IsLocated (Annot a SourceSpan) where 
  srcPos = ann


instance PP Fact where
  pp (PhiVar x)       = text "phi"  <+> pp x
  pp (FunInst ts θ)   = text "inst" <+> pp ts <+> text " " <+> pp θ
  pp (LocInst l)      = text "loc inst" <+> pp l
  pp (WorldInst l)    = text "world inst" <+> pp l
  pp (Assume t)       = text "assume" <+> pp t
  pp (AssumeH h)      = text "assume heap" <+> pp h
  pp (Rename ls)    = text "Loc Rename" <+> pp ls
  pp (Delete ls)    = text "Loc Delete" <+> pp ls
  pp (WindInst l wls i αs ls) = pp (l:wls)
                            <+> pp αs
                            <+> pp ls
                            <+> text "⇑" <+> pp i
  pp (UnwindInst l i ls) = pp l <+> text "⇓" <+> pp i <+> pp ls
  

instance (F.Reftable r, PP r) => PP (Fact_ r) where
  pp (PhiVar x)     = text "phi"  <+> pp x
  pp (FunInst ts θ) = text "inst" <+> pp ts <+> text " " <+> pp θ
  pp (LocInst l)    = text "loc inst" <+> pp l 
  pp (WorldInst l)  = text "world inst" <+> pp l
  pp (Assume t)     = text "assume" <+> pp t
  pp (AssumeH h)    = text "assume heap" <+> pp h
  pp (Rename ls)    = text "Loc Rename" <+> pp ls
  pp (Delete ls)    = text "Loc Delete" <+> pp ls
  pp (WindInst l wls i αs ls) = pp (l:wls)
                            <+> pp αs
                            <+> pp ls
                            <+> text "⇑" <+> pp i
  pp (UnwindInst l i ls) = pp l <+> text "⇓" <+> pp i <+> pp ls

instance (F.Reftable r, PP r) => PP (AnnInfo_ r) where
  pp             = vcat . (ppB <$>) . M.toList 
    where 
      ppB (x, t) = pp x <+> dcolon <+> pp t

instance (PP a, PP b) => PP (Annot b a) where
  pp (Ann x ys) = text "Annot: " <+> pp x <+> pp ys

isAsm  :: Fact -> Bool
isAsm  (Assume _)  = True
isAsm  (AssumeH _) = True
isAsm  _           = False

-----------------------------------------------------------------------
-- | Primitive / Base Types -------------------------------------------
-----------------------------------------------------------------------

tVar   :: (F.Reftable r) => TVar -> RType r
tVar   = (`TVar` mempty) 

tInt, tBool, tUndef, tNull, tString, tVoid, tErr :: (F.Reftable r) => RType r
tInt    = TApp TInt     [] [] mempty 
tBool   = TApp TBool    [] [] mempty
tString = TApp TString  [] [] mempty
tTop    = TApp TTop     [] [] mempty
tVoid   = TApp TVoid    [] [] mempty
tUndef  = TApp TUndef   [] [] mempty
tNull   = TApp TNull    [] [] mempty
tErr    = tVoid
tFunErr = ([],[],[],heapEmpty,heapEmpty,B returnSymbol tErr)

tRef :: (F.Reftable r) => Location -> RType r
tRef l  = TApp (TRef l) [] [] mempty

-- tProp :: (F.Reftable r) => RType r
-- tProp  = TApp tcProp [] F.top 
-- tcProp = TDef $ F.S propConName 

-----------------------------------------------------------------------
-- | Operator Types ---------------------------------------------------
-----------------------------------------------------------------------


-----------------------------------------------------------------------
infixOpTy :: InfixOp -> Env t -> t 
-----------------------------------------------------------------------
infixOpTy o g = fromMaybe err $ envFindTy ox g
  where 
    err       = errorstar $ printf "Cannot find infixOpTy %s" (ppshow ox) -- (ppshow g)
    ox        = infixOpId o

infixOpId OpLT       = builtinId "OpLT"
infixOpId OpLEq      = builtinId "OpLEq"
infixOpId OpGT       = builtinId "OpGT"
infixOpId OpGEq      = builtinId "OpGEq"
infixOpId OpEq       = builtinId "OpEq"
infixOpId OpStrictEq = builtinId "OpSEq"
infixOpId OpNEq      = builtinId "OpNEq"
infixOpId OpLAnd     = builtinId "OpLAnd"
infixOpId OpLOr      = builtinId "OpLOr"
infixOpId OpSub      = builtinId "OpSub"
infixOpId OpAdd      = builtinId "OpAdd"
infixOpId OpMul      = builtinId "OpMul"
infixOpId OpDiv      = builtinId "OpDiv"
infixOpId OpMod      = builtinId "OpMod"
infixOpId o          = errorstar $ "Cannot handle: infixOpId " ++ ppshow o

-----------------------------------------------------------------------
prefixOpTy :: PrefixOp -> Env t -> t 
-----------------------------------------------------------------------
prefixOpTy o g = fromMaybe err $ envFindTy (prefixOpId o) g
  where 
    err       = convertError "prefixOpTy" o

prefixOpId PrefixMinus  = builtinId "PrefixMinus"
prefixOpId PrefixLNot   = builtinId "PrefixLNot"
prefixOpId PrefixTypeof = builtinId "PrefixTypeof"
prefixOpId PrefixDelete = builtinId "PrefixDelete"
prefixOpId o            = errorstar $ "Cannot handle: prefixOpId " ++ ppshow o

builtinId       = mkId . ("builtin_" ++)

rawStringSymbol = F.Loc F.dummyPos . F.stringSymbol
rawStringFTycon = F.stringFTycon . F.Loc F.dummyPos
