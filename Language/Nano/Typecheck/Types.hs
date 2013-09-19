-- | Global type definitions for Refinement Type Checker

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE NoMonomorphismRestriction   #-}

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
  , RHeap
  , RType (..)
  , Bind (..)
  , toType
  , ofType
  , strengthen 
  , strengthenContainers 

  -- * Helpful checks
  , isTop, isNull, isUndefined, isObj, isUnion

  -- * Constructing Types
  , mkUnion, mkUnionR

  -- * Deconstructing Types
  , bkFun
  , funHeaps
  , bkAll
  , bkUnion, rUnion, rTypeR, setRTypeR
  , noUnion, unionCheck

  -- * Regular Types
  , Type
  , BHeap
  , TBody (..)
  , TVar (..)
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
  ) where 

import           Text.Printf
import           Data.Hashable
import           Data.Maybe                     (fromMaybe)
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

instance F.Symbolic a => F.Symbolic (Located a) where 
  symbol = F.symbol . val

-- | Constructed Type Bodies
data TBody r 
   = TD { td_con  :: !TCon          -- TDef name ...
        , td_args :: ![TVar]        -- Type variables
        , td_heap :: !(RHeap r)     -- An existentially quantified heap
        , td_body :: !(RType r)     -- int or bool or fun or object ...
        , td_pos  :: !SourceSpan    -- Source position
        } deriving (Eq, Ord, Show, Functor, Data, Typeable)

-- | Type Constructors
data TCon 
  = TInt                   
  | TBool                
  | TString
  | TVoid             
  | TTop
  | TRef Location
  | TDef  (Id SourceSpan)
  | TUn
  | TNull
  | TUndef
    deriving (Ord, Show, Data, Typeable)

type RHeap r = Heap (RType r)    

-- | (Raw) Refined Types 
data RType r  
  = TApp  TCon [RType r]                         r
  | TVar  TVar                                   r 
  | TFun  [Bind r] (RType r) (RHeap r) (RHeap r) r
  | TObj  [Bind r]                               r
  | TBd   (TBody r)
  | TAll  TVar (RType r)
    deriving (Ord, Show, Functor, Data, Typeable)


data Bind r
  = B { b_sym  :: F.Symbol
      , b_type :: !(RType r)
      } 
    deriving (Eq, Ord, Show, Functor, Data, Typeable)


-- | Standard Types
type Type    = RType ()
type BHeap   = RHeap ()

-- | Stripping out Refinements 
toType :: RType a -> Type
toType = fmap (const ())
  
-- | Adding in Refinements
ofType :: (F.Reftable r) => Type -> RType r
ofType = fmap (const F.top)

locs :: RType r -> [Location]
locs t             = L.nub (go t)
  where
    go (TApp c ts _) = locs' c ++ (concatMap go ts)
    go (TObj bs _)   = concatMap (go . b_type) bs
    go _             = []

locs' :: TCon -> [Location]
locs' (TRef l) = [l]
locs' _        = []

-- | RHeap utils
restrictHeap :: (F.Reftable r) => [Location] -> RHeap r -> RHeap r
restrictHeap [] h = heapEmpty
restrictHeap ls h = heapCombine [restrictHeap ls' (heapFromBinds nbs), heapFromBinds bs]
  where
    (bs,nbs) = L.partition ((`elem` ls) . fst) $ heapBinds h
    ls'      = concatMap (filter (not . (`elem` ls)) . locs . snd) bs

bkFun :: RType r -> Maybe ([TVar], [Bind r], RHeap r, RHeap r, RType r)
bkFun t = do let (αs, t') = bkAll t
             (xts, t'', h, h')  <- bkArr t'
             return        (αs, xts, h, h', t'')

bkArr (TFun xts t h h' _) = Just (xts, t, h, h')
bkArr _                   = Nothing

bkAll                :: RType a -> ([TVar], RType a)
bkAll t              = go [] t
  where 
    go αs (TAll α t) = go (α : αs) t
    go αs t          = (reverse αs, t)

funHeaps :: RType r -> Maybe (RHeap r, RHeap r)
funHeaps = (stripHeaps =<<) . bkFun
  where
    stripHeaps (_,_,σ,σ',_) = return (σ,σ')

---------------------------------------------------------------------------------
mkUnion :: (Ord r, Eq r, F.Reftable r) => [RType r] -> RType r
---------------------------------------------------------------------------------
mkUnion = mkUnionR F.top


---------------------------------------------------------------------------------
mkUnionR :: (Ord r, Eq r, F.Reftable r) => r -> [RType r] -> RType r
---------------------------------------------------------------------------------
mkUnionR _ [ ] = tErr
mkUnionR _ [t] = t       
mkUnionR r ts  = case ts' of
                   [t] -> t
                   _   -> TApp TUn ts' r
  where ts' = L.sort $ L.nub ts

---------------------------------------------------------------------------------
bkUnion :: RType r -> [RType r]
---------------------------------------------------------------------------------
bkUnion (TApp TUn xs _) = xs
bkUnion t               = [t]


-- | Strengthen the top-level refinement

---------------------------------------------------------------------------------
strengthen                   :: F.Reftable r => RType r -> r -> RType r
---------------------------------------------------------------------------------
{-strengthen t = setRTypeR t . (rTypeR t `F.meet`)-} 
-- The above does not handle cases other than TApp and TVar correctly
strengthen (TApp c ts r) r'  = TApp c ts $ r' `F.meet` r 
strengthen (TVar α r)    r'  = TVar α    $ r' `F.meet` r 
strengthen t _               = t                         

-- NOTE: r' is the OLD refinement. 
--       We want to preserve its VV binder as it "escapes", 
--       e.g. function types. Sigh. Should have used a separate function binder.


-- | Strengthen the refinement of a type @t2@ deeply, using the 
-- refinements of an equivalnet (having the same raw version) 
-- type @t1@
-- TODO: Add checks for equivalence in union and objects
strengthenContainers (TApp TUn ts r) (TApp TUn ts' r') =
  TApp TUn (zipWith strengthenContainers ts ts') $ r' `F.meet` r
strengthenContainers (TObj ts r) (TObj ts' r') = 
  TObj (zipWith doB ts ts') $ r' `F.meet` r
  where 
    doB (B s t) (B s' t') | s == s' =  B s $ strengthenContainers t t'
    doB _       _                   = errorstar "strengthenContainers: sanity check - 1"
strengthenContainers t t' | toType t == toType t' = strengthen t' $ rTypeR t
strengthenContainers _ _  | otherwise = errorstar "strengthenContainers: sanity check - 2"
  


---------------------------------------------------------------------------------
-- | Helpful type checks
---------------------------------------------------------------------------------

-- | Top-level Top (any) check
isTop :: RType r -> Bool
isTop (TApp TTop _ _)   = True 
isTop (TApp TUn  ts _ ) = any isTop ts
isTop _                 = False

isUndefined :: RType r -> Bool
isUndefined (TApp TUndef _ _)   = True 
isUndefined _                   = False

isNull :: RType r -> Bool
isNull (TApp TNull _ _)   = True 
isNull _                  = False

isObj :: RType r -> Bool
isObj (TObj _ _)        = True
isObj _                 = False

isUnion :: RType r -> Bool
isUnion (TApp TUn _ _) = True           -- top-level union
isUnion _              = False

-- Get the top-level refinement for unions - use Top (True) otherwise
-- TODO: Fill up for other types
rUnion               :: F.Reftable r => RType r -> r
rUnion (TApp TUn _ r) = r
rUnion _              = F.top
 
-- Get the top-level refinement 
rTypeR :: RType r -> r
rTypeR (TApp _ _ r) = r
rTypeR (TVar _ r)   = r
rTypeR (TFun _ _ _ _ r) = r
rTypeR (TObj _ r)   = r
rTypeR (TBd  _)     = errorstar "Unimplemented: rTypeR - TBd"
rTypeR (TAll _ _ )  = errorstar "Unimplemented: rTypeR - TAll"

setRTypeR :: RType r -> r -> RType r
setRTypeR (TApp c ts _) r'   = TApp c ts r'
setRTypeR (TVar v _)    r'   = TVar v r'
setRTypeR (TFun xts ot ih oh _) r' = TFun xts ot ih oh r'
setRTypeR (TObj xts _)  r'   = TObj xts r'
setRTypeR (TBd  _)     _     = errorstar "Unimplemented: setRTypeR - TBd"
setRTypeR (TAll _ _ )  _     = errorstar "Unimplemented: setRTypeR - TAll"


---------------------------------------------------------------------------------------
noUnion :: (F.Reftable r) => RType r -> Bool
---------------------------------------------------------------------------------------
noUnion (TApp TUn _ _)      = False
noUnion (TApp _  rs _)      = and $ map noUnion rs
noUnion (TFun bs rt h h' _) = and $ map noUnion $ rt : ((map b_type bs) ++ heapTypes h ++ heapTypes h')
noUnion (TObj bs    _)      = and $ map noUnion $ map b_type bs 
noUnion (TBd  _      )      = error "noUnion: cannot have TBodies here"
noUnion (TAll _ t    )      = noUnion t
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
  TApp TUn t1 _          == TApp TUn t2 _         = (null $ t1 L.\\ t2) && (null $ t2 L.\\ t1)
    {-tracePP (printf "Diff: %s \\ %s" (ppshow $ L.nub t1) (ppshow $ L.nub t2)) $-}
  TApp c1 t1s r1         == TApp c2 t2s r2        = (c1, t1s, r1)  == (c2, t2s, r2)
  TVar v1 r1             == TVar v2 r2            = (v1, r1)       == (v2, r2)
  TFun b1 t1 hi1 ho1 r1  == TFun b2 t2 hi2 ho2 r2 = (b1, t1, hi1, ho1, r1) == (b2, t2, hi2, ho2, r2)
  TObj b1 r1             == TObj b2 r2            = (null $ b1 L.\\ b2) && (null $ b2 L.\\ b1) && r1 == r2
  TBd (TD c1 a1 h1 b1 _) == TBd (TD c2 a2 h2 b2 _)= (c1, a1, h1, b1)   == (c2, a2, h2, b2)
  TAll _ _               == TAll _ _              = undefined -- TODO
  _                      == _                     = False



---------------------------------------------------------------------------------
-- | Nano Program = Code + Types for all function binders
---------------------------------------------------------------------------------

data Nano a t = Nano { code   :: !(Source a)        -- ^ Code to check
                     , specs  :: !(Env t)           -- ^ Imported Specifications
                     , defs   :: !(Env t)           -- ^ Signatures for Code
                     , consts :: !(Env t)           -- ^ Measure Signatures 
                     , tDefs  :: !(Env t)           -- ^ Type definitions
                     , quals  :: ![F.Qualifier]     -- ^ Qualifiers
                     , invts  :: ![Located t]       -- ^ Type Invariants
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
    $+$ text "********************** QUALS *********************"
    $+$ F.toFix (quals  pgm) 
    $+$ text "********************** INVARIANTS ****************"
    $+$ pp (invts pgm) 
    $+$ text "**************************************************"
    
instance Monoid (Nano a t) where 
  mempty        = Nano (Src []) envEmpty envEmpty envEmpty envEmpty [] [] 
  mappend p1 p2 = Nano ss e e' cs tds qs is 
    where 
      ss        = Src $ s1 ++ s2
      Src s1    = code p1
      Src s2    = code p2
      e         = envFromList ((envToList $ specs p1) ++ (envToList $ specs p2))
      e'        = envFromList ((envToList $ defs p1)  ++ (envToList $ defs p2))
      cs        = envFromList $ (envToList $ consts p1) ++ (envToList $ consts p2)
      tds       = envFromList $ (envToList $ tDefs p1) ++ (envToList $ tDefs p2)
      qs        = quals p1 ++ quals p2
      is        = invts p1 ++ invts p2

mapCode :: (a -> b) -> Nano a t -> Nano b t
mapCode f n = n { code = fmap f (code n) }


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

instance F.Reftable r => PP (RType r) where
  pp (TVar α r)                 = F.ppTy r $ pp α 
  pp (TFun xts t h h' _)        = ppArgs parens comma xts
                              <+> text "/" <+> pp h
                              <+> text "=>"
                              <+> pp t <+> text "/" <+> pp h'
  pp t@(TAll _ _)               = text "forall" <+> ppArgs id space αs <> text "." 
                                   <+> pp t' where (αs, t') = bkAll t
  pp (TApp TUn ts r)            = F.ppTy r $ ppArgs id (text "+") ts 
  pp (TApp d@(TDef _)ts r)      = F.ppTy r $ ppTC d <+> ppArgs brackets comma ts 

  pp (TApp c [] r)              = F.ppTy r $ ppTC c 
  pp (TApp c ts r)              = F.ppTy r $ parens (ppTC c <+> ppArgs id space ts)  
  pp (TObj bs _ )               = ppArgs braces comma bs
  pp (TBd (TD (TDef id) v h r _)) = pp (F.symbol id) <+> ppArgs brackets comma v
                                                     <+> text "∃!"
                                                     <+> pp h
                                                     <+> text ". "
                                                     <+> pp r
  pp (TBd _)                    = error "This is not an acceptable form for TBody" 

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
  hashWithSalt s (TDef z)    = hashWithSalt s (8 :: Int) + hashWithSalt s z
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
  = PhiVar  !(Id SourceSpan) 
  | FunInst ![(TVar,RType r)] ![(Location,Location)]
  | LocInst !Location
  | Assume  !(RType r)
  | AssumeH !(RHeap r)
  | Unwind  !Location
  | Wind    !(Location, Id SourceSpan, Id SourceSpan, Id SourceSpan)
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
  pp (Assume t)       = text "assume" <+> pp t
  pp (AssumeH h)      = text "assume heap" <+> pp h

instance (F.Reftable r, PP r) => PP (Fact_ r) where
  pp (PhiVar x)     = text "phi"  <+> pp x
  pp (FunInst ts θ) = text "inst" <+> pp ts <+> text " " <+> pp θ
  pp (LocInst l)    = text "loc inst" <+> pp l 
  pp (Assume t)     = text "assume" <+> pp t
  pp (AssumeH h)    = text "assume heap" <+> pp h

instance (F.Reftable r, PP r) => PP (AnnInfo_ r) where
  pp             = vcat . (ppB <$>) . M.toList 
    where 
      ppB (x, t) = pp x <+> dcolon <+> pp t

instance (PP a, PP b) => PP (Annot b a) where
  pp (Ann x ys) = text "Annot: " <+> pp x <+> pp ys

isAsm  :: Fact -> Bool
isAsm  (Assume _) = True
isAsm  _          = False

-----------------------------------------------------------------------
-- | Primitive / Base Types -------------------------------------------
-----------------------------------------------------------------------

tVar   :: (F.Reftable r) => TVar -> RType r
tVar   = (`TVar` F.top) 

tInt, tBool, tUndef, tNull, tString, tVoid, tErr :: (F.Reftable r) => RType r
tInt    = TApp TInt     [] F.top 
tBool   = TApp TBool    [] F.top
tString = TApp TString  [] F.top
tTop    = TApp TTop     [] F.top
tVoid   = TApp TVoid    [] F.top
tUndef  = TApp TUndef   [] F.top
tNull   = TApp TNull    [] F.top
tErr    = tVoid
tFunErr = ([],[],heapEmpty,heapEmpty,tErr)

tRef :: (F.Reftable r) => Location -> RType r
tRef l  = TApp (TRef l) [] F.top

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
prefixOpId o            = errorstar $ "Cannot handle: prefixOpId " ++ ppshow o

builtinId       = mkId . ("builtin_" ++)

