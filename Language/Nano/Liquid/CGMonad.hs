{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | Operations pertaining to Constraint Generation

module Language.Nano.Liquid.CGMonad (
    
  -- * Constraint Generation Monad
    CGM

  -- * Constraint Information
  , CGInfo (..)

  -- * Execute Action and Get FInfo
  , getCGInfo 

  -- * Get Defined Function Type Signature
  , getDefType

  -- * Get Defined Types
  , getTDefs
  , getMEnv
  , getMeasures
  , getRMeasures
  , addMeasuresM
    
  -- * Get Current Function
  , getFun, withFun

  -- * Throw Errors
  , cgError      

  -- * Fresh Templates for Unknown Refinement Types 
  , freshTyFun
  , freshTyInst
  , freshPredInst 
  , freshTyPhis
  , freshTyWind
  , freshObjBinds
  , freshHeapEnv

  , strengthenObjBinds

  -- * Freshable
  , Freshable (..)

  -- * Environment API
  , envAddFresh
  , envAddFieldBinders
  , envAdds
  , tyAddNNInv
  , envAddFreshHeap
  , envFreshHeapBind
  , envAddReturn
  , envAddGuard
  , envFindTy, envFindTy'
  , envFindTyDef
  , envToList
  , envFindReturn
  , envJoin
  , concretizeLoc

  -- * Add Subtyping Constraints
  , subTypes, subTypes', subType, subType'
  , subTypeContainers, subTypeContainers'
  , subTypeHeaps
  , subTypeWind
  , subTypeWUpdate
  , alignTsM, withAlignedM
  , strengthenUnion

  , addInvariant
  , updateFieldM
  
  -- * Add Type Annotations
  , addAnnot

  -- * Unfolding
  , unfoldSafeCG, unfoldFirstCG

  -- * Util
  , renameHeapBinds 

  ) where

import           Data.Maybe                     (fromMaybe)
import           Data.Function                  (on)
import           Data.List
import           Data.Tuple                     (swap)
import           Data.Ord
import           Data.Monoid                    (mempty)
import           Data.Traversable               (traverse)
import qualified Data.HashMap.Strict            as M

-- import           Language.Fixpoint.PrettyPrint
import           Text.PrettyPrint.HughesPJ

import           Language.Nano.Types
import           Language.Nano.Errors
import qualified Language.Nano.Annots           as A
import qualified Language.Nano.Env              as E
import           Language.Nano.Misc
import           Language.Nano.Typecheck.Types 
import           Language.Nano.Typecheck.Heaps 
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Unify
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Liquid.Types
import           Language.Nano.Liquid.Measures
import           Language.Nano.Liquid.Predicates
import           Language.Nano.Liquid.Qualifiers

import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Names (propConName)
import           Language.Fixpoint.Misc
import           Control.Applicative 

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Error
import           Text.Printf 

import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Parser        (SourceSpan (..))
import           Language.ECMAScript3.PrettyPrint

import           Debug.Trace                        (trace)

-------------------------------------------------------------------------------
-- | Top level type returned after Constraint Generation ----------------------
-------------------------------------------------------------------------------

data CGInfo = CGI { cgi_finfo :: F.FInfo Cinfo
                  , cgi_annot :: A.AnnInfo RefType  
                  }

-- Dump the refinement subtyping constraints
instance PP CGInfo where
  pp (CGI finfo _) = cat (map pp (M.elems $ F.cm finfo))

instance PP (F.SubC c) where
  pp s = pp (F.lhsCs s) <+> text " <: " <+> pp (F.rhsCs s)



-------------------------------------------------------------------------------
getCGInfo :: Config -> Nano AnnTypeR RefType -> CGM a -> CGInfo
-------------------------------------------------------------------------------
getCGInfo cfg pgm = clear . cgStateCInfo pgm . execute cfg pgm . (>> fixCWs)
  where 
    fixCWs          = (,) <$> fixCs <*> fixWs
    fixCs           = get >>= concatMapM splitC . map flattenRecords . cs
    fixWs           = get >>= concatMapM splitW . ws

execute :: Config -> Nano AnnTypeR RefType -> CGM a -> (a, CGState)
execute cfg pgm act
  = case runState (runErrorT act) $ initState cfg pgm of 
      (Left err, _) -> errorstar err
      (Right x, st) -> (x, st)  

initState       :: Config -> Nano AnnTypeR RefType -> CGState
initState c pgm = CGS F.emptyBindEnv Nothing (defs pgm) (consts pgm) (tDefs pgm) (tMeas pgm) (tRMeas pgm) [] [] 0 mempty invs c 
  where 
    invs = M.fromList [(tc, t) | t@(Loc _ (TApp tc _ _ _)) <- invts pgm]

getDefType f 
  = do m <- cg_defs <$> get
       maybe err return $ E.envFindTy f m 
    where 
       err = cgError l $ errorMissingSpec l f
       l   = srcPos f

-- cgStateFInfo :: Nano a1 (RType F.Reft)-> (([F.SubC Cinfo], [F.WfC Cinfo]), CGState) -> CGInfo
cgStateCInfo pgm ((fcs, fws), cg) = CGI (patchSymLits fiQs) (cg_ann cg)
  where 
    fiQs = {- inferQuals -} fi
    fi   = F.FI { F.cm    = M.fromList $ F.addIds fcs  
                , F.ws    = fws
                , F.bs    = binds cg
                , F.gs    = consFPBinds (count cg) pgm 
                , F.lits  = []
                , F.kuts  = F.ksEmpty
                , F.quals = quals . inferQualsFromTypes (F.fromListSEnv fieldFuns) . inferQualsFromSpec $ pgm 
                }


patchSymLits fi = fi { F.lits = F.symConstLits fi ++ F.lits fi }
    
---------------------------------------------------------------------------------------
getTDefs :: CGM (E.Env RefType)
---------------------------------------------------------------------------------------
getTDefs  = cg_tdefs <$> get

---------------------------------------------------------------------------------------
getMEnv :: CGM (E.Env RefType)            
---------------------------------------------------------------------------------------
getMEnv   = cg_meas <$> get

---------------------------------------------------------------------------------------
getMeasures :: CGM [Measure]
---------------------------------------------------------------------------------------
getMeasures = cg_tmeas <$> get >>= (return . map snd . M.toList)

---------------------------------------------------------------------------------------
getRMeasures :: (F.Symbolic s) => s -> CGM [Measure]             
---------------------------------------------------------------------------------------
getRMeasures t = do m <- cg_trmeas <$> get
                    return $ M.lookupDefault [] (F.symbol t) m

addMeasuresM g b
    = do γt    <- getTDefs
         γm    <- getMEnv
         ms    <- getMeasures
         return $ addMeasures γm γt ms σ b
       where
         σ      = bind <$> rheap g
         bind x = B (locSym x) (locTy "addMeasuresM" g x) 
---------------------------------------------------------------------------------------
getFun :: CGM F.Symbol
---------------------------------------------------------------------------------------
getFun = cg_fun <$> get >>= maybe err return
  where err = error "BUG: no current function!"
        
---------------------------------------------------------------------------------------
withFun :: F.Symbol -> CGM a -> CGM a
---------------------------------------------------------------------------------------
withFun f m = do fOld <- cg_fun <$> get
                 modify $ \st -> st { cg_fun = Just f }
                 r <- m
                 modify $ \st -> st { cg_fun = fOld }
                 return r

---------------------------------------------------------------------------------------
-- measureBinds   ::  Nano a (RType RReft) -> F.SEnv F.SortedReft
---------------------------------------------------------------------------------------
-- nilB n      = [(nilSymbol, F.RR (F.FVar $ fromIntegral $ n + 1) mempty)]

-- Oh the horrors REMOVE ME!!!!
strSort = F.FApp (F.strFTyCon) []
fieldFuns = [(F.val $ fieldSym (tInt :: Type), F.RR (F.FFunc 1 [F.FVar 0, strSort, F.FInt]) mempty)
            ,(F.val $ fieldSym (tRef "l" :: Type),F.RR (F.FFunc 1 [F.FVar 0, strSort, rawStr "Ref"]) mempty)
            ,(F.symbol "field_T",F.RR (F.FFunc 1 [F.FVar 0, strSort, rawStr "T"]) mempty)]
nilB n      = [(nilSymbol, F.RR (rawStr "T") mempty)]
              
rawStr s = F.FApp (F.stringFTycon . F.Loc F.dummyPos $ s) []

measureBinds   = map tx . E.envToList . consts 
  where tx (id, t) = (F.symbol id, rTypeSortedReft t)

predicateBinds = pappSymSorts

consFPBinds n pgm = F.fromListSEnv (fieldFuns ++ {- nilB n ++ -} measureBinds pgm ++ predicateBinds)
                 
---------------------------------------------------------------------------------------
-- | Constraint Generation Monad ------------------------------------------------------
---------------------------------------------------------------------------------------

data CGState 
  = CGS { binds    :: F.BindEnv            -- ^ global list of fixpoint binders
        , cg_fun   :: !(Maybe F.Symbol)    -- ^ current function
        , cg_defs  :: !(E.Env RefType)     -- ^ type sigs for all defined functions
        , cg_meas  :: !(E.Env RefType)     -- ^ type sigs for measures
        , cg_tdefs :: !(E.Env RefType)     -- ^ type definitions
        , cg_tmeas :: !(M.HashMap F.Symbol Measure)   -- ^ (regular) measure definitions
        , cg_trmeas:: !(M.HashMap F.Symbol [Measure]) -- ^ (recursive) type measure definitions
        , cs       :: ![SubC]              -- ^ subtyping constraints
        , ws       :: ![WfC]               -- ^ well-formedness constraints
        , count    :: !Integer             -- ^ freshness counter
        , cg_ann   :: A.AnnInfo RefType    -- ^ recorded annotations
        , invs     :: TConInv              -- ^ type constructor invariants
        , cg_opts  :: Config               -- ^ configuration options
        }

type CGM     = ErrorT String (State CGState)

type TConInv = M.HashMap TCon (Located RefType)

---------------------------------------------------------------------------------------
cgError :: (IsLocated l) => l -> String -> CGM a 
---------------------------------------------------------------------------------------
cgError l msg = throwError $ printf "CG-ERROR at %s : %s" (ppshow $ srcPos l) msg

---------------------------------------------------------------------------------------
-- | Environment API ------------------------------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
envAddFresh :: (IsLocated l) => l -> RefType -> CGEnv -> CGM (Id l, CGEnv) 
---------------------------------------------------------------------------------------
envAddFresh l t g 
  = do x  <- freshId l
       g' <- envAdds [(x, t)] g
       return (x, g')

---------------------------------------------------------------------------------------
envAdds      :: (F.Symbolic x, IsLocated x) => [(x, RefType)] -> CGEnv ->CGM CGEnv
---------------------------------------------------------------------------------------
envAdds xts' g
  = do xts    <- zipWith (\x t -> (x, strengthenObjBinds x (tyAddNNInv g t))) xs <$> mapM addInvariant ts
       let g' =  g { renv = E.envAdds xts        (renv g) } 
       xts'   <- mapM (xtwrap $ addMeasuresM g') xts
       is     <- forM xts' $  addFixpointBind 
       _      <- forM xts' $  \(x, t) -> addAnnot (srcPos x) x t
       return $ g' { renv = E.envAdds xts'       (renv g')}
                   { fenv = F.insertsIBindEnv is (fenv g) }
    where 
      (xs,ts)        = unzip xts'
      xtwrap m (x,t) = m (B (F.symbol x) t) >>= \(B _ t') -> return (x,t')
                       
tyAddNNInv g t 
  = case locs t of
      [l] -> if heapMem l h then 
               t `strengthen` (ureft $ F.predReft (F.pOr [veq, heq l]))
             else t
      _ -> t
    where
      h   = rheap g
      -- veq = mkProp $ F.EApp (F.Loc F.dummyPos $ F.symbol "nil") [F.eVar (F.vv Nothing)]
      veq = isNil (F.vv Nothing)
      heq l = F.PNot (isNil (heapReadSym "tyAddNNInv" l h))
      -- heq l = F.PNot (mkProp (F.EApp (F.Loc F.dummyPos $ F.symbol "nil") [F.eVar (heapReadSym "tyAddNNInv" l h)]))
              
      -- veq = F.PAtom F.Eq (F.eVar (F.vv Nothing)) (F.expr (F.symbol "null"))
      -- heq l = F.PAtom F.Ne (F.eVar (heapReadSym "tyAddNNInv" l h)) (F.expr (F.symbol "null"))
                       
---------------------------------------------------------------------------------------
envAddFreshHeap   :: (IsLocated l) => l -> (Location, RefType) -> CGEnv -> CGM (Id SourceSpan, CGEnv)
---------------------------------------------------------------------------------------
envAddFreshHeap l lt g
  = do x           <- freshId (srcPos l) 
       g'          <- envAdds [(x, snd lt)] g
       return $ (x, g' { rheap = heapCombineWith const [heapBinders [(fst lt, x)] , rheap g'] })
  where heapBinders = refHeapFromBinds "envAddHeap" 

envFreshHeapBind :: (IsLocated l) => l -> Location -> CGEnv -> CGM (Id SourceSpan, CGEnv)
envFreshHeapBind l j g
  = freshId (srcPos l) >>= (\i -> return $ (i, g { rheap = newHeap i }))
    where
      newHeap i   = heapCombineWith const [heapBinders [(j,i)], rheap g]
      heapBinders = refHeapFromBinds "envAddHeap" 

addFixpointBind :: (F.Symbolic x) => (x, RefType) -> CGM F.BindId
addFixpointBind (x, t) 
  = do let s     = F.symbol x
       let r     = rTypeSortedReft $ flattenRecord t
       (i, bs') <- F.insertBindEnv s r . binds <$> get 
       modify    $ \st -> st { binds = bs' }
       return    $ i

---------------------------------------------------------------------------------------
addInvariant   :: RefType -> CGM RefType
---------------------------------------------------------------------------------------
addInvariant t           = ((`tx` t) . invs) <$> get
  where 
    -- HACK!!
    fixRef (TRef _)        = TRef "l"
    fixRef tc              = tc
    tx i t@(TApp tc _ _ _) = maybe t (strengthen t . ureft . rTypeReft . val) $ M.lookup (fixRef tc) i
    tx _ t                 = t 


---------------------------------------------------------------------------------------
addAnnot       :: (F.Symbolic x) => SourceSpan -> x -> RefType -> CGM () 
---------------------------------------------------------------------------------------
addAnnot l x t = modify $ \st -> st {cg_ann = A.addAnnot l x t (cg_ann st)}

---------------------------------------------------------------------------------------
envAddReturn        :: (IsLocated f)  => f -> RefType -> CGEnv -> CGEnv 
---------------------------------------------------------------------------------------
envAddReturn f t g  = g { renv = E.envAddReturn f t (renv g) } 

---------------------------------------------------------------------------------------
envAddGuard       :: (F.Symbolic x, IsLocated x) => x -> Bool -> CGEnv -> CGEnv  
---------------------------------------------------------------------------------------
envAddGuard x b g = g { guards = guard b x : guards g }
  where 
    guard True    = F.eProp 
    guard False   = F.PNot . F.eProp
    -- Falsy values:
    -- ∙ false
    -- ∙ 0 (zero)
    -- ∙ "" (empty string)
    -- ∙ null
    -- ∙ undefined
    -- ∙ NaN (Not a number)

    -- guard True  v = F.eProp v
    -- guard False v = F.pOr [ F.PNot (F.eProp v) 
    --                         
    --                      ] 
    --   where
    --     vEqX x    = F.PAtom F.Eq (F.eVar v) x
                           
---------------------------------------------------------------------------------------
envFindTyDef  :: Id SourceSpan -> CGM (RHeapEnv RReft, F.Symbol, RefType, [TVar], [PVar Type])
---------------------------------------------------------------------------------------
envFindTyDef ty
  = do γ <- getTDefs
       case E.envFindTy ty γ of
         Just (TBd t) -> 
           return (td_heap t,
                   td_self t,
                   td_body t,
                   td_args t,
                   td_refs t)
         Nothing -> error "BARF!!!"
---------------------------------------------------------------------------------------
envFindTy     :: (IsLocated x, F.Symbolic x, F.Expression x) => x -> CGEnv -> RefType 
---------------------------------------------------------------------------------------
-- | A helper that returns the actual @RefType@ of the expression by
--     looking up the environment with the name, strengthening with
--     singleton for base-types.

envFindTy x g = (`eSingleton` x) $ fromMaybe err $ E.envFindTy x $ renv g
  where 
    err       = errorstar $ bugUnboundVariable (srcPos x) (F.symbol x)
                    
---------------------------------------------------------------------------------------
envFindTy'     :: (F.Symbolic x, F.Expression x) => x -> CGEnv -> RefType 
---------------------------------------------------------------------------------------
envFindTy' x g = (`eSingleton` x) $ fromMaybe err $ E.envFindTy x $ renv g
  where 
    err       = errorstar $ bugUnboundVariable dummySpan (F.symbol x)


---------------------------------------------------------------------------------------
envToList     ::  CGEnv -> [(Id SourceSpan, RefType)]
---------------------------------------------------------------------------------------
envToList g = E.envToList $ renv g


---------------------------------------------------------------------------------------
envFindReturn :: CGEnv -> RefType 
---------------------------------------------------------------------------------------
envFindReturn = E.envFindReturn . renv


----------------------------------------------------------------------------------
envJoin :: AnnTypeR -> CGEnv -> Maybe CGEnv -> Maybe CGEnv -> CGM (Maybe CGEnv)
----------------------------------------------------------------------------------
envJoin _ _ Nothing x           = return x
envJoin _ _ x Nothing           = return x
envJoin l g (Just g1) (Just g2) = Just <$> envJoin' l g g1 g2 

----------------------------------------------------------------------------------
envJoin' :: AnnTypeR -> CGEnv -> CGEnv -> CGEnv -> CGM CGEnv
----------------------------------------------------------------------------------

-- HINT: 1. use @envFindTy@ to get types for the phi-var x in environments g1 AND g2
--       2. use @freshTyPhis@ to generate fresh types (and an extended environment with 
--          the fresh-type bindings) for all the phi-vars using the unrefined types 
--          from step 1.
--       3. generate subtyping constraints between the types from step 1 and the fresh types
--       4. return the extended environment.

envJoin' l g g1 g2
  = do  {- td      <- E.envMap toType <$> cg_tdefs <$> get -}
        let xs   = [x | PhiVar x <- ann_fact l] 
            t1s  = (`envFindTy` g1) <$> xs 
            t2s  = (`envFindTy` g2) <$> xs
        when (length t1s /= length t2s) $ cgError l (bugBadPhi l t1s t2s)
        γ       <- getTDefs
        let t4   = zipWith (compareTs γ) t1s t2s
        (g',ts) <- freshTyPhis (srcPos l) g xs $ toType <$> fst4 <$> t4
        -- To facilitate the sort check t1s and t2s need to change to their
        -- equivalents that have the same sort with the joined types (ts) (with
        -- the added False's to make the types equivalent
        g1' <- envAdds (zip xs $ snd4 <$> t4) g1 
        g2' <- envAdds (zip xs $ thd4 <$> t4) g2

        zipWithM_ (subTypeContainers l g1') [envFindTy x g1' | x <- xs] ts
        zipWithM_ (subTypeContainers l g2') [envFindTy x g2' | x <- xs] ts
        
        g'  <- joinHeaps l γ g' g1' g2'

        return g'

joinHeaps l γ g g1 g2
  = do let (σ1,σ2)          = mapPair rheap (g1,g2)
           (one',both,two') = heapSplit σ1 σ2
           one              = filter (`elem` heapLocs (rheap g)) one'
           two              = filter (`elem` heapLocs (rheap g)) two'
           t1s              = map (flip (heapReadType g1 "joinHeaps") σ1) both
           t2s              = map (flip (heapReadType g2 "joinHeaps") σ2) both
           t4               = zipWith (compareTs γ) t1s t2s
       ts                  <- mapM (freshTy "joinHeaps" . toType . fst4) t4
       xs                  <- mapM (const (freshId (srcPos l))) ts
       g'                  <- envAdds (zipWith str xs ts) g
       _                   <- mapM (wellFormed l g') ts
       g'                  <- foldM foldFresh g' (zip xs ts)
       let σj               = refHeapFromTyBinds "joinHeaps σj" $ zip both xts
           xts              = zipWith B (F.symbol <$> xs) ts
           su1              = F.mkSubst $ zip (xsyms xs) (evars σ1 both)
           su2              = F.mkSubst $ zip (xsyms xs) (evars σ2 both)
       -- Subtype the common heap locations
       subTypeHeaps l g1 σ1 ((F.subst su1 <$>) <$> σj)
       subTypeHeaps l g2 σ2 ((F.subst su2 <$>) <$> σj)
       g'' <- foldM (\g j -> concretizeLoc l "joinHeaps" j g) (g' { rheap = σj }) both
       -- zipWithM_ (subType l g1) (map snd4 t4) (map (F.subst su1 <$>) ts)
       -- zipWithM_ (subType l g2) (map thd4 t4) (map (F.subst su2 <$>) ts)
       -- zipWithM_ (subTypeContainers l g1) (map snd4 t4) (map (F.subst su1 <$>) ts)
       -- zipWithM_ (subTypeContainers l g2) (map thd4 t4) (map (F.subst su2 <$>) ts)
       xs'                 <- mapM (const (freshId (srcPos l))) xs
       -- g'                  <- envAdds (zip xs' (reverse ts')) g'
       return $ g' { rheap = rheap g'' }
           
    where
      xsyms xs           = F.symbol <$> xs
      evars σ ls         = map (F.eVar . flip (heapReadSym "joinHeaps") σ) ls
      foldFresh g (x,t)  = freshObjBinds l g x t
      str x t            = (x, strengthenObjBinds x t)
      rdHeap             = heapRead "joinHeaps"
          
concretizeLoc l msg loc g = do
  g <- freshObjBinds l g x $ strengthenObjBinds x xt
  envAdds [(x, xt)] $ g { rheap = σ' }
  -- (xt', g') <- freshObjBinds l x g $ strengthenObjBinds x xt
  -- envAdds [(x, xt' `eSingleton` x)] $ g' { rheap = σ' }
  where
    (x, xt, σ') = refHeapMakeConc msg loc (rheap g)


-- freshSubHeap l σ g_wf g locs
--   = do let (xs,ts) = unzip $ map (safeRefReadHeap "freshSubHeap safe" g σ) locs
--        xs'    <- mapM (const (freshId (srcPos l))) xs
--        ts'    <- mapM (freshTy "freshSubHeap") ts
--        mapM (wellFormed l g_wf) ts'
--        return (xs', ts')
           
---------------------------------------------------------------------------------------
-- | Fresh Templates ------------------------------------------------------------------
---------------------------------------------------------------------------------------
       
-- | Instantiate Fresh Type (at Function-site)
---------------------------------------------------------------------------------------
freshTyFun :: CGEnv -> AnnTypeR -> Id AnnTypeR -> RefType -> CGM RefType 
---------------------------------------------------------------------------------------
freshTyFun g l f t = freshTyFun' g l f t . kVarInst . cg_opts =<< get  

-- A "trivial" type may nevertheless include abstract refinements. 
-- Therefore, when creating a fresh fun type, let's first instantiate
freshTyFun' g l _ t b
  | isTrivialRefType t && b = freshTy "freshTyFun" t >>= \t -> wellFormed l g t
  | otherwise = return t


-- | Instantiate Fresh Type (at Call-site)

---------------------------------------------------------------------------------------
-- freshTyInst :: (IsLocated l) => l -> CGEnv -> [TVar] -> [Type] -> RefType -> CGM RefType 
-- freshTyInst :: AnnTypeR -> CGEnv -> [TVar] -> [Type] -> RefType -> CGM RefType 
---------------------------------------------------------------------------------------
freshTyInst l g αs τs tbody
  = do let (vs,πs,bs,hi,ho,ro) = maybe (error "freshTyInst: not a function") id $ bkFun tbody
       xr                  <- freshId l
       let retsu            = F.mkSubst [(rs, F.eVar xr)]
           B rs rt          = ro
       -- (hisu, hi')         <- freshHeapEnv l hi
       (hosu, ho')         <- freshHeapEnv l ({- (F.subst hisu <$>) <$> -} ho)
       let su               = retsu `F.catSubst` {- hisu `F.catSubst` -} hosu
       ts                  <- mapM (freshTy "freshTyInst") (F.subst su <$> τs)
       _                   <- mapM (wellFormed l g . fmap stripSubsHack) ts
       let θ                = fromLists (zip αs ts) []
           rs'              = F.symbol xr
           rt'              = F.subst su rt
           heapSu           = (fmap (F.subst su) <$>)
           tbody' = TFun (suBind su <$> bs) (B rs' rt') (hi) ((F.subst retsu <$>)<$> ho') mempty
       return $ {- tracePP msg $ -} apply θ tbody'
    where
       suBind su b = F.subst su <$> b
       msg = printf "freshTyInst αs=%s τs=%s: " (ppshow αs) (ppshow τs)

freshPredInst l g πs tbody
  = do πs'   <- mapM (freshPredRef l g) πs
       return $ replacePreds tbody $ zip πs πs'

freshPredRef :: (IsLocated l) => l -> CGEnv -> PVar Type -> CGM (PRef Type RReft RefType)
freshPredRef l g (PV _ _ t as)
  = do t    <- freshTy "freshPredRef" t 
       args <- mapM (const fresh) as
       let targs = [(x,s) | (x, (s, y, z)) <- zip args as, (F.EVar y) == z]
       g' <- envAdds [(x, ofType t) | (x, t) <- targs] g
       wellFormed l g' t
       return $ PPoly targs t
-- | Instantiate Fresh Type (at Wind-site)
--------------------------------------------------------------------------------------
freshTyWind :: (PP l, IsLocated l) => 
               CGEnv -> l -> RSubst RReft -> Id SourceSpan
               -> CGM (RefHeap, (F.Symbol, RefType), RefType, [Measure])
---------------------------------------------------------------------------------------
freshTyWind g l θ ty
  = do (σ,s,t,vs,πs) <- envFindTyDef ty
       γ             <- getTDefs
       let (αs,ls)    = toLists θ
       θ'            <- flip fromLists ls <$> mapM freshSubst αs
       let θα         = uncurry fromLists . fmap (const []) $ toLists θ'
       (su,σ')       <- freshHeapEnv l $ apply θ' σ
       ms            <- (instMeas su <$>) <$> getRMeasures ty
       πs'           <- mapM (freshPredRef l g) πs
       let tApp       = mkApp (apply θ' . tVar <$> vs) πs'
           psu        = zip πs (apply θ' πs')
       return (mapLocTy (exp γ θα psu) <$> refHeap σ',
               (s, exp γ θα psu $ apply θ' $ F.subst su t),
               exp γ θα [] tApp,
               ms)
    where 
      -- traceType m t        = tracePP m (toType t) `seq` t
      exp γ θ su           = subPvs su . apply θ . expandTApp γ 
      expBi γ θ su (B x t) = B x $ exp γ θ su t
      instMeas su (id, syms, e1,e2) = (id, syms, F.subst su e1,F.subst su e2)
      s                    = srcPos l
      toId                 = Id s . F.symbolString . b_sym                      
      toIdTyPair b         = (toId b, b_type b)
      mkApp vs πs          = TApp (TDef ty) vs πs mempty
      freshSubst (α,τ)     = do τ <- freshTy "freshTyWind" τ
                                _ <- wellFormed l g $ stripSubsHack <$> τ
                                return (α,τ)
      subPvs su t          = foldl' (flip substPred) t su 

stripSubsHack (F.Reft (vv,refas) `U` p) = F.Reft (vv,refas') `U` p
  where refas' = go <$> refas
        go (F.RKvar k _) = F.RKvar k mempty
        go p             = p

-- | Instantiate Fresh Type (at Phi-site) 
---------------------------------------------------------------------------------------
freshTyPhis :: (PP l, IsLocated l) => l -> CGEnv -> [Id l] -> [Type] -> CGM (CGEnv, [RefType])  
---------------------------------------------------------------------------------------
freshTyPhis l g xs τs 
  = do ts <- mapM    (freshTy "freshTyPhis")  ({-tracePP "From" -} τs)
       g' <- envAdds (safeZip "freshTyPhis" xs ts) g
       _  <- mapM    (wellFormed l g') ts
       return (g', ts)

       
-- freshObjBinds takes an object { ...f:T... }
-- and: 1. creates a new binding xf:T in g,
--      2. returns a new object { ...f:T'...} with
--         T' = {v = xf}

-- NEW: freshObjBinds creates  binder with reft (v = x.f) for each (f:T in { ...f:T ... })
---------------------------------------------------------------------------------------
freshObjBinds :: (PP l, IsLocated l, F.Symbolic a) => l -> CGEnv -> a -> RefType -> CGM CGEnv
---------------------------------------------------------------------------------------
freshObjBinds l g x t@(TObj _ _)
  = do let TObj bs _ = strengthenObjBinds x . rType $ t
       let xs        = b_sym <$> bs
       xs'     <- mapM (refreshId l) xs
       envAdds (safeZip "freshObjBinds" xs' (b_type <$> bs)) g
       -- let bs' = safeZip "freshOBjBinds'" xs $ map (\x -> flip envFindTy g') xs'
       -- return (TObj [ B (F.symbol x) t | (x,t) <- bs' ] r, g')
       -- let bs' = tracePP "bs'" [ B (b_sym b) ((`eSingleton` x) $ rType $ b_type b) |  (x,b) <- (zip xs' $ tracePP " BS" bs)]
       -- return g'

freshObjBinds _ g _ _
  = return g

---------------------------------------------------------------------------------------
freshHeapEnv :: (PP l, IsLocated l) => l -> RHeapEnv RReft -> CGM (F.Subst, RHeapEnv RReft)
---------------------------------------------------------------------------------------
freshHeapEnv l σ
  = do let xs  = b_sym <$> heapTypes σ
       xs'     <- mapM (refreshId (srcPos l)) xs
       let su  = F.mkSubst $ zip (F.symbol <$> xs) (F.eVar . F.symbol <$> xs')
       return $ (su, heapBind . zipUp (replace su) xs' $ heapBinds σ)
    where
      heapBind                 = heapFromBinds "freshHeapEnv"
      zipUp                    = safeZipWith "freshHeapEnv"
      replace su x' (l, B x t) = (l, B (F.symbol x') (F.subst su t))


strengthenObjBinds x (TObj bs r)
  = TObj (f <$> bs) r
  where
    f (B b t) = B b $ eSingleton t (field x b t)

strengthenObjBinds _ t = t

-- loc |-> x, x.f := y
---------------------------------------------------------------------------------------
updateFieldM :: (PP l, IsLocated l, F.Symbolic f) =>
  l -> Location -> CGEnv -> f -> Id l -> CGM CGEnv
---------------------------------------------------------------------------------------
updateFieldM l m g f y
  = do let t_obj        = envFindTy x g
           t_fld        = envFindTy y g
           x            = heapReadSym "updateField" m $ rheap g
       let t_obj'       = updateField (envFindTy y g) s t_obj
       t_objm          <- addMeasObjBinds g t_obj'
       (x', g')        <- envFreshHeapBind l m g
       g'' <- envAdds [(x', t_objm)] g'
       freshObjBinds l g'' x' t_objm
    where   
      s           = F.symbol f
      deref x t b = t `eSingleton` (field x b t)

addMeasObjBinds g (TObj bs r)                    
    = mapM (addMeasuresM g) bs >>= \bs' -> return (TObj bs' r)

------------------------------------------------------------------------
-- | Converting records (flattening for constraints)
------------------------------------------------------------------------
flattenRecords :: SubC -> SubC
flattenRecords c@(Sub e si lhs rhs) = 
  -- Sub (e { renv = g }) si (tracePP "FLATTENED" $ flattenRecord (tracePP "ORIGINAL" lhs)) (flattenRecord rhs)
  Sub (e { renv = g }) si lhs rhs
  where
    g = E.envMap flattenRecord (renv e)
      
flattenRecord :: RefType -> RefType 
flattenRecord (TObj bs r) = TObj bs (foldl F.meet r rs)
  where
    F.Reft (vv, _) = F.toReft r
    rs = ureft . mkRecReft vv <$> bs
         
flattenRecord t = t
                 
mkRecReft v (B f t) = (F.Reft (v, F.subst sub p))
  where 
    F.RR so (F.Reft (vv, p)) = rTypeSortedReft t
    sub = F.mkSubst [(vv, (field v f t :: F.Expr ))]

-- HACK
field x y t = F.EApp (fieldSym t) [F.expr $ F.symbol x, bind2sym y]
  where bind2sym = F.ESym . F.SL . F.symbolString
        

fieldSym t = F.dummyLoc $ F.symbol ("field_" ++ tname t)
  where
    tname = render . F.toFix . clear . rTypeSort
  
---------------------------------------------------------------------------------------
-- | Adding Subtyping Constraints -----------------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
subTypes :: (IsLocated x, F.Expression x, F.Symbolic x) 
         => AnnTypeR -> CGEnv -> [x] -> [RefType] -> CGM ()
---------------------------------------------------------------------------------------
subTypes l g xs ts = zipWithM_ (subType l g) [envFindTy x g | x <- xs] ts


subTypes' msg l g xs ts = zipWithM_ (subType' msg l g) [envFindTy x g | x <- xs] ts

-- | Subtyping

-- Also adds invariants
-- XXX: Are the invariants added for types nested in containers (i.e. unions and
-- objects)? Probably not, so this process should be done after the splitC.

---------------------------------------------------------------------------------------
subType :: AnnTypeR -> CGEnv -> RefType -> RefType -> CGM ()
---------------------------------------------------------------------------------------
subType l g t1 t2 =
  do tt1   <- addInvariant t1
     tt2   <- addInvariant t2
     tdefs <- getTDefs
     let s  = checkTypes tdefs tt1 tt2
     modify $ \st -> st {cs = c s : (cs st)}
  where
    c      = uncurry $ Sub g (ci l)
    checkTypes tdefs t1 t2 | equivWUnions tdefs t1 t2 = (t1,t2)
    checkTypes  _ t1 t2    | otherwise                = errorstar $ msg t1 t2
    msg t1 t2 = printf "[%s]\nCGMonad: checkTypes not aligned: \n%s\nwith\n%s"
                  (ppshow $ ann l) (ppshow $ toType t1) (ppshow $ toType t2)

-- A more verbose version
subType' msg l g t1 t2 = 
  subType l g (trace (printf "SubType[%s]:\n\t%s\n\t%s" msg (ppshow t1) (ppshow t2)) t1) t2

-------------------------------------------------------------------------------
subTypeHeaps :: AnnTypeR -> CGEnv -> RefHeap -> RefHeap -> CGM ()
-------------------------------------------------------------------------------
subTypeHeaps l g σ1 σ2
  = mapM_ subTypeLoc (s ++ s2)
    where
      (s1, s, s2)    = heapSplit σ1 σ2
      subTypeLoc loc = if heapMem loc σ1 then
                         subTypeField l g False
                                (heapReadSym "subTypeHeaps(a)" loc σ1, 
                                             heapReadType g "subTypeHeaps(a)" loc σ1)
                                            (heapReadType g "subTypeHeaps(b)" loc σ2)
                       else do
                         let t = heapReadType g "subTypeHeaps(b)" loc σ2
                         x <- freshId (srcPos l)
                         tnull <- nullTypeOfType x t
                         g <- envAdds [(x,tnull)] g
                         subTypeField l g True
                                (x, tnull) t
    
subTypeField l g b (x1,t1) t2 = do 
  g_st <- freshObjBinds l g (F.symbol x1) t1
  withAlignedM (doSubType g_st) t1 t2
  where doSubType g_st t1 t2 = subTypeContainers l g_st (if b then (eSingleton t1 x1) else t1) t2 

-- nullTypeOfType :: (IsLocated l) => Id l -> RefType -> CGM RefType
nullTypeOfType x t = predsNullType x t'
  where
    vNew = F.vv Nothing
    t' = setRTypeR t (ureft $ F.predReft (isNil vNew))
    r  = rTypeR $ rType t
        
predsNullType x (TApp c@(TDef _) ts rs r) 
  = do γ <- cg_tdefs <$> get 
       let as = typeRefArgs γ c
       let rs = map go as 
           θ  = fromLists (safeZip "predNull" (typeVarArgs γ c) (fmap F.top <$> ts)) []
       return (TApp c (tNNull <$> ts) (apply θ rs) r) :: CGM RefType
  where
    go v = PPoly [] $ tNNull $ ofType $ pv_ty v
    go v = PPoly [(s, t) | (t, s, _) <- pv_as v] $ tNNull $ ofType $ pv_ty v
    tNNull t = t `strengthen` (ureft $ F.predReft (F.PNot (isNil x))) :: RefType

predsNullType _ t = return t
                        

-------------------------------------------------------------------------------
equivWUnions :: E.Env RefType -> RefType -> RefType -> Bool
-------------------------------------------------------------------------------
equivWUnions γ t1@(TApp TUn _ _ _) t2@(TApp TUn _ _ _) = 
  {-let msg = printf "In equivWUnions:\n%s - \n%s" (ppshow t1) (ppshow t2) in -}
  case unionPartsWithEq (equiv γ) t1 t2 of 
    (ts,[],[])  -> and $ uncurry (safeZipWith "equivWUnions" $ equivWUnions γ) (unzip ts)
    _           -> False
equivWUnions γ t t' = equiv γ t t'

equivWUnionsM t t' = getTDefs >>= \γ -> return $ equivWUnions γ t t'



-- | Subtyping container contents: unions, objects. Includes top-level

-- `subTypeContainers` breaks down container types (unions and objects) to their
-- sub-parts and recursively creates subtyping constraints for these parts. It
-- returns simple subtyping for the rest of the cases (non-container types).
--
-- The top-level refinements of the container types strengthen the parts.
--
--      Γ |- {v:T1 | P1 ∧ P3}       <: { v:T1 | P1' ∧ P3'}
--      Γ |- {v:T2 | P2 ∧ P3}       <: { v:T2 | P2' ∧ P3'}
--      −−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−−   
--      Γ |- {v:T1/P1 + T2/P2 | P3} <: {v:T1/P1' + T2/P2' | P3'}
--
--
-- TODO: Will loop infinitely for cycles in type definitions
--
-------------------------------------------------------------------------------
subTypeRecursive :: AnnTypeR -> CGEnv -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeRecursive l g t1@(TApp d1@(TDef _) _ _ _) t2@(TApp d2@(TDef _) _ _ _)
    | d1 /= d2 = do γ <- getTDefs
                    let ((σ1',b1,θ1),(σ2',b2,θ2)) = mapPair (unfoldSafeEnv γ) (t1,t2)
                        (σ1, σ2)                = mapPair refHeap (σ1', σ2')
                        (B x1 t1', B x2 t2')    = (apply θ1 b1, apply θ2 b2)
                        bsub                    = F.mkSubst [(x2, F.eVar x1)] -- x2 := x1
                    (g, heapSub, σ2r)           <- renameHeapBinds l g σ1 σ2
                    let su                      = F.catSubst heapSub bsub
                        xts                     = toIdTy l x1 t1' : (map btop $ heapTypes σ1')
                    g_st                       <- envAdds xts g
                    subTypeContainers l g_st t1' (F.subst su t2')
                    subTypeHeaps l g_st σ1 (mapLocTy replaceC <$> σ2r)
    where
      replaceC t@(TApp d ts rs r) | d == d2   = TApp d1 ts rs r
      replaceC t                  | otherwise = t
      btop (B x t)                            = toIdTy l x t
      toIdTy l x t                            = (Id (srcPos l) (F.symbolString x), t)

-------------------------------------------------------------------------------
subTypeContainers :: AnnTypeR -> CGEnv -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeContainers l g t1@(TApp d@(TDef _) ts _ _) t2@(TApp d'@(TDef _) ts' _ _)
  | d == d'   = do subType l g t1 t2 
                   mapM_ (uncurry $ subTypeContainers l g) $ zip ts ts'
  | otherwise = subTypeRecursive l g t1 t2

subTypeContainers l g t1 t2@(TApp (TDef _) _ _ _) = 
  unfoldSafeCG t2 >>= \t2' -> subTypeContainers l g t1 t2'

subTypeContainers l g t1@(TApp (TDef _) _ _ _) t2 = 
  unfoldSafeCG t1 >>= \t1' -> subTypeContainers l g t1' t2

subTypeContainers l g u1@(TApp TUn _ _ _) u2@(TApp TUn _ _ _) = 
  getTDefs >>= \γ -> sbs $ bkPaddedUnion "subTypeContainers" γ u1 u2
  where        
    (r1, r2)     = mapPair rTypeR        (u1, u2)
    -- Fix the ValueVar of the top-level refinement to be the same as the
    -- Valuevar of the part
    fix t b v    | v == b    = rTypeValueVar t
                 | otherwise = v
    rr t r       = F.subst1 r (b, F.eVar $ rTypeValueVar t) where F.Reft (b,_) = ur_reft r
    sb  (t1 ,t2) = subTypeContainers l g (t1 `strengthen` rr t1 r1)
                                         (t2 `strengthen` rr t2 r2)
    sbs ts       = mapM_ sb ts

-- TODO: the environment for subtyping each part of the object should have the
-- tyopes for the rest of the bindings
subTypeContainers l g o1@(TObj _ _) o2@(TObj _ _) = 
  do subType l g o1 o2
     getTDefs >>= \γ -> sbs $ bkPaddedObject o1 o2
  where
    sbs          = mapM_ sb
    (r1, r2)     = mapPair rTypeR (o1, o2)
    -- Fix the ValueVar of the top-level refinement 
    -- to be the same as the Valuevar of the part
    fix t b v    | v == b    = rTypeValueVar t
                 | otherwise = v
    rr t r       = F.subst1 r (b, F.eVar $ rTypeValueVar t) where F.Reft (b,_) = r
    sb (t1 ,t2)  = subTypeContainers l g t1 t2

subTypeContainers l g t1 t2 = subType l g t1 t2


subTypeContainers' msg l g t1 t2 = 
  subTypeContainers l g (tracePP (printf "subTypeContainers[%s]:\n\t%s\n\t%s" 
                                msg (ppshow t1) (ppshow t2)) t1) t2

alignAndStrengthen msg l g u1@(TApp TUn _ _ _) u2@(TApp TUn _ _ _) =
  getTDefs >>= return . (\γ -> bkPaddedUnion msg γ u1' u2')
  where 
    (u1',u2') = mapPair strengthenUnion (u1,u2)
 
alignAndStrengthen msg l g t1 t2 = return [(t1, t2)]

------------------------------------------------------------------------------------------
renameHeapBinds :: AnnTypeR -> CGEnv -> RefHeap -> RefHeap -> CGM (CGEnv, F.Subst, RefHeap)
------------------------------------------------------------------------------------------
renameHeapBinds l g σ1 σ2
  = do -- reshYs <- mapM (refreshId l) nys
       let nilYTs = map (rType) nyts 
       (nxs, g') <- foldM go ([], g) (zip nil nilYTs)
       let su     =F.mkSubst $ reverse $ (zip ys xs ++ zip nys (F.eVar . F.symbol <$> nxs))
       -- g' <- envAdds (zip freshYs nilYTs) g 
       return (g', su, (F.subst su <$>) <$> σ2)
  where l1s = heapLocs σ1
        l2s = heapLocs σ2
        ls  = filter (`elem` l2s) l1s
        nil = filter (`notElem` l1s) l2s
        xs  = F.eVar . lx σ1 <$> ls
        ys  = lx σ2 <$> ls
        nys = map (lx σ2) nil
        nyts= map (flip (heapReadType g "renameHeapBinds(a)") σ2) nil
        -- su  = F.mkSubst $ (zip ys xs ++ (zip nys (repeat (F.eVar nilSymbol))))
        str t = setRTypeR t (ureft $ F.predReft (isNil (F.vv Nothing)))
        lx  = flip (heapReadSym "renameHeapBinds")
        go (xs, g) (j,t) = do (x,g) <- envFreshHeapBind l j g
                              t <- nullTypeOfType x (str $ rType t)
                              g <- envAdds [(x,t)] g
                              return ((x:xs), g)
------------------------------------------------------------------------------------------
strengthenUnion :: RefType -> RefType
------------------------------------------------------------------------------------------
strengthenUnion (TApp TUn ts rs r) = TApp TUn (map fixup ts) rs r
  where fix t b v
          | v == b    = rTypeValueVar t
          | otherwise = v
        rr t r  = F.subst1 r (b, F.eVar $ rTypeValueVar t) where F.Reft (b,_) = ur_reft r
        -- rr t r  = F.substa (fix t b) r where F.Reft (b,_) = r
        fixup t = t `strengthen` rr t r

strengthenUnion t = t

-------------------------------------------------------------------------------
alignTsM :: RefType -> RefType -> CGM (RefType, RefType)
-------------------------------------------------------------------------------
alignTsM t t' = getTDefs >>= \g -> return $ alignTs g t t'


-------------------------------------------------------------------------------
withAlignedM :: (RefType -> RefType -> CGM a) -> RefType -> RefType -> CGM a
-------------------------------------------------------------------------------
withAlignedM f t t' = alignTsM t t' >>= uncurry f 
 

-- | Monadic unfolding
-------------------------------------------------------------------------------
unfoldFirstCG :: RefType -> CGM RefType
-------------------------------------------------------------------------------
unfoldFirstCG t = getTDefs >>= \γ -> return $ unfoldFirst γ t


-------------------------------------------------------------------------------
unfoldSafeCG :: RefType -> CGM RefType
-------------------------------------------------------------------------------
unfoldSafeCG   t = getTDefs >>= \γ -> return $ snd3 $ unfoldSafe γ t


---------------------------------------------------------------------------------------
-- | Adding Well-Formedness Constraints -----------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
wellFormed       :: (IsLocated l) => l -> CGEnv -> RefType -> CGM RefType  
---------------------------------------------------------------------------------------
wellFormed l g t = do modify $ \st -> st { ws = (W g (ci l) t) : ws st }
                      return t



---------------------------------------------------------------------------------------
-- | Generating Fresh Values ----------------------------------------------------------
---------------------------------------------------------------------------------------

class Freshable a where
  fresh   :: CGM a
  true    :: a -> CGM a
  true    = return . id
  refresh :: a -> CGM a
  refresh = return . id

instance Freshable Integer where
  fresh = do modify $ \st -> st { count = 1 + (count st) }
             count <$> get 

instance Freshable F.Symbol where
  fresh     = F.tempSymbol "nano" <$> fresh
  refresh _ = fresh

instance Freshable String where
  fresh     = F.symbolString <$> fresh

freshId   :: (IsLocated l) => l -> CGM (Id l)
freshId l = Id l <$> fresh

refreshId :: (F.Symbolic s, IsLocated l) => l -> s -> CGM (Id l)
refreshId l s = (Id l . F.symbolString) <$> (refresh $ F.symbol s)        

freshTy :: RefTypable a => s -> a -> CGM RefType
freshTy _ τ = refresh $ rType τ

instance Freshable F.Refa where
  fresh = (`F.RKvar` F.emptySubst) <$> (F.intKvar <$> fresh)

instance Freshable [F.Refa] where
  fresh = single <$> fresh

instance Freshable F.Reft where
  fresh                  = errorstar "fresh Reft"
  true    (F.Reft (v,_)) = return $ F.Reft (v, []) 
  refresh (F.Reft (_,_)) = curry F.Reft <$> ({-tracePP "freshVV" <$> -}freshVV) <*> fresh
    where freshVV        = F.vv . Just  <$> fresh

instance Freshable RReft where
  fresh                  = errorstar "fresh RReft"
  true    (U r _)        = ureft   <$> true r
  refresh (U r p)        = (`U` p) <$> refresh r
                           
instance Freshable F.SortedReft where
  fresh                  = errorstar "fresh Reft"
  true    (F.RR so r)    = F.RR so <$> true r 
  refresh (F.RR so r)    = F.RR so <$> refresh r

instance Freshable RefType where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

trueRefType    :: RefType -> CGM RefType
trueRefType    = mapReftM true true

refreshRefType :: RefType -> CGM RefType
refreshRefType (TAll α t)  = TAll α  <$> refresh t

refreshRefType (TAllP π t) = TAllP π <$> refresh t

refreshRefType t@(TApp _ _ _ _) 
  = do γ              <- getTDefs
       TApp c ts rs r <- mapReftM refresh refresh $ expandTApp γ t
       let πas         = typeRefArgs γ c
       let (rs',rest)  = splitAt (length πas) rs
       let rπs         = safeZip "refreshRef" rs' πas
       let r'          = foldl go r rest
       TApp c ts <$> (mapM refreshRef rπs) <*> pure r'
  where
    go r (PMono _ r') = r' `F.meet` r
    go r _            = error "ASDF"

refreshRefType t@(TFun _ _ _ _ _)
  = mapReftM refresh return t

refreshRefType t 
  = mapReftM refresh refresh t
                  
refreshHeapEnv h = do bs' <- mapM refreshBind bs
                      return $ heapFromBinds "refreshHeapEnv "(zip ls bs')
  where lbs = heapBinds h
        bs  = snd <$> lbs
        ls  = fst <$> lbs

refreshBind (B x t) = refresh t >>= \t -> return $ B x t

refreshRef (PPoly s t, π) = PPoly <$> (mapM freshSym (pv_as π)) <*> refreshRefType t
refreshRef (PMono _ _, _) = errorstar "refreshRef: PMono unexpected"
                            
freshSym s = liftM (, fst3 s) fresh
---------------------------------------------------------------------------------------
-- | Splitting Subtyping Constraints --------------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
splitC' :: SubC -> CGM [FixSubC]
---------------------------------------------------------------------------------------
splitC c = splitC' c

---------------------------------------------------------------------------------------
-- | Function types
---------------------------------------------------------------------------------------
splitC' (Sub g i tf1@(TFun xt1s t1 σi1 σo1 _) tf2@(TFun xt2s t2 σi2 σo2 _))
  = do let bcs    = bsplitC g i tf1 tf2
           tf2xts = xt2s ++ heapTypes σi2
           tf1obs = heapTypes σo1
       g'        <- envTyAdds i tf2xts g 
       cs        <- concatMapM splitC $ safeZipWith "splitC1" (Sub g' i) t2s t1s' 
       g''       <- envTyAdds i tf1obs g'
       cs'       <- splitC $ Sub g'' i (F.subst su (b_type t1)) (b_type t2)      
       cs''      <- concatMapM splitC $ safeZipWith "splitC2" (Sub g' i) σi2ts σi1ts
       cs'''     <- concatMapM splitC $ safeZipWith "splitC3" (Sub g'' i) σo1ts σo2ts
       return     $ bcs ++ cs ++ cs' ++ cs'' ++ cs'''
    where 
       -- Stack Variables/Types
       t2s        = b_type <$> xt2s
       t1s'       = F.subst su (b_type <$> xt1s)
       -- Heap Variables/Types
       σi2ts      = b_type . snd <$> σi2bs
       σi1ts      = F.subst su (b_type . snd <$> σi1bs)
       σi1bs      = sortHBs σi1
       σi2bs      = sortHBs σi2

       σo1ts      = b_type . snd <$> σo1bs
       σo2ts      = F.subst su (b_type . snd <$> σo2bs)
       σo1bs      = sortHBs σo1
       σo2bs      = sortHBs σo2
       -- Substitution Calculation
       su         = asu `F.catSubst` hisu `F.catSubst` hosu
       asu        = F.mkSubst $ safeZipWith "splitC4" bSub xt1s xt2s
       hisu       = F.mkSubst $ safeZipWith "splitC5" hSub σi1bs σi2bs
       hosu       = F.mkSubst $ safeZipWith "splitC5" hSub σo2bs σo1bs
       bSub b1 b2 = (b_sym b1, F.eVar $ b_sym b2)
       hSub b1 b2 = bSub (snd b1) (snd b2)
       sortHBs    = sortBy (compare `on` fst) . heapBinds

---------------------------------------------------------------------------------------
-- | TAlls
---------------------------------------------------------------------------------------
splitC' (Sub g i (TAll α1 t1) (TAll α2 t2))
  | α1 == α2 
  = splitC $ Sub g i t1 t2
  | otherwise   
  = splitC $ Sub g i t1 t2' 
  where 
    θ   = fromLists [(α2, tVar α1 :: RefType)] []
    t2' = apply θ t2

---------------------------------------------------------------------------------------
-- | TVars
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TVar α1 _) t2@(TVar α2 _)) 
  | α1 == α2
  = return $ bsplitC g i t1 t2
  | otherwise
  = errorstar "UNEXPECTED CRASH in splitC"

---------------------------------------------------------------------------------------
-- | Unions:
-- We need to get the bsplitC for the top level refinements 
-- Nothing more should be added, the internal subtyping constrains have been
-- dealt with separately
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TApp TUn _ _ _) t2@(TApp TUn _ _ _)) =
  ifM (equivWUnionsM t1 t2) 
    (return    $ bsplitC g i t1 t2) 
    (errorstar $ printf "Unequal unions in splitC: %s - %s" (ppshow $ toType t1) (ppshow $ toType t2))

splitC' (Sub _ _ t1@(TApp TUn _ _ _) t2) = 
  errorstar $ printf "Unions in splitC: %s - %s" (ppshow t1) (ppshow t2)
splitC' (Sub _ _ t1 t2@(TApp TUn _ _ _)) = 
  errorstar $ printf "Unions in splitC: %s - %s" (ppshow t1) (ppshow t2)

---------------------------------------------------------------------------------------
-- |Type definitions
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TApp d1@(TDef _) t1s r1s _) t2@(TApp d2@(TDef _) t2s r2s _)) | d1 == d2
  = do  let cs = bsplitC g i t1 t2
        -- constructor parameters are covariant
        cs'   <- concatMapM splitC $ safeZipWith "splitcTDef" (Sub g i) t1s t2s
        cs''  <- concatMapM (rsplitC g i) $ safeZip "splitC'" r1s r2s
        return $ cs ++ cs' ++ cs''

splitC' (Sub _ _ (TApp (TDef _) _ _ _) (TApp (TDef _) _ _ _))
  = errorstar "Unimplemented: Check type definition cycles"
  
splitC' (Sub g i t1@(TApp (TDef _) _ _ _) t2) = 
  unfoldSafeCG t1 >>= \t1' -> splitC' $ Sub g i t1' t2

splitC' (Sub g i  t1 t2@(TApp (TDef _) _ _ _)) = 
  unfoldSafeCG t2 >>= \t2' -> splitC' $ Sub g i t1 t2'

---------------------------------------------------------------------------------------
-- | Rest of TApp
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TApp _ t1s _ _) t2@(TApp _ t2s _ _))
  = do let cs = bsplitC g i t1 t2
       cs'   <- concatMapM splitC $ safeZipWith 
                                    (printf "splitC4: %s - %s" (ppshow t1) (ppshow t2)) 
                                    (Sub g i) t1s t2s
       return $ cs ++ cs'

---------------------------------------------------------------------------------------
-- | Objects
-- Just the top-level constraint will be included here
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TObj _ _ ) t2@(TObj _ _ ))
  = return $ bsplitC g i t1 t2

splitC' (Sub _ _ t1 t2@(TObj _ _ ))
  = error $ printf "splitC - should have been broken down earlier:\n%s <: %s" 
            (ppshow t1) (ppshow t2)

splitC' (Sub _ _ t1@(TObj _ _ ) t2)
  = error $ printf "splitC - should have been broken down earlier:\n%s <: %s" 
            (ppshow t1) (ppshow t2)


splitC' x 
  = cgError (srcPos x) $ bugBadSubtypes x 

rsplitC γ i (PMono _ _, PMono _ _)
  = cgError (srcPos i) "rsplitC on PMono"

rsplitC γ i (t1@(PPoly s1 r1), t2@(PPoly s2 r2))
  = do γ' <- envAdds ((ofType <$>) <$> s2) γ
       splitC $ Sub γ' i (F.subst su r1) r2
  where
    su = F.mkSubst [(x, F.eVar y) | ((x,_),(y,_)) <- zip s1 s2]

rsplitC _ i (ref1, ref2)
  = cgError (srcPos i) $ printf "Can't split:\n%s\n%s" (ppshow ref1) (ppshow ref2)

---------------------------------------------------------------------------------------
bsplitC :: (F.Reftable r) => CGEnv -> a -> RType r -> RType r -> [F.SubC a]
---------------------------------------------------------------------------------------
bsplitC g ci t1 t2
  | F.isFunctionSortedReft r1 && F.isNonTrivialSortedReft r2
  = [F.subC (fenv g) F.PTrue (r1 {F.sr_reft = mempty}) r2 Nothing [] ci]
  | F.isNonTrivialSortedReft r2
  = [F.subC (fenv g) p r1 r2 Nothing [] ci]
  | otherwise
  = {- tracePP "bsplitC trivial" -} []
  where
    p  = F.pAnd $ guards g
    r1 = rTypeSortedReft t1
    r2 = rTypeSortedReft t2
    
subTypeWUpdate l g tobj tobj'
  = do γ            <- getTDefs
       (tt,tl,tr,_) <- return $ compareTs γ tobj tobj'
       t            <- freshTy "weak" (toType tt) 
       (x,g')       <- envAddFresh l t g
       wellFormed l g' t
       subTypeContainers l g' tobj  t
       subTypeContainers l g' tobj' t
       return (x,g') 

    

{-            
   Winding up the heap: 
     Σ = Σ₁ * Σ₂ * l ↦ T@{ ... xᵢ:Tᵢ ... }
   Into
     Σ = Σ₁' * l ↦ C[α...]
   Where
     C[α...] = ∃! Σ₂' . l ↦ T'@{ ... xᵢ:Tᵢ' ... } 

   Renaming/Consumption of locations is permitted...

   Constraints:
     Γ ⊢ T <: T'   %% Normal subtyping on folded record
     for each i, ∀ l ∈ loc(Tᵢ'), Γ,x:Ti ⊢ Σ₁|l <: Σ₂|l
-}
-------------------------------------------------------------------------------
subTypeWind :: AnnTypeR -> CGEnv -> RefHeap -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeWind = subTypeWind' [] 

subTypeWind' seen l g σ t1 t2
    = {- tracePP msg () `seq` -} withAlignedM (subTypeWindTys seen l g σ) t1 t2
  where
    msg = printf "subTypeWind %s/%s <: %s/%s\n==\n%s <: %s" 
          (ppshow t1) (ppshow (rheap g)) (ppshow t2) (ppshow σ)
          (ppshow $ toType t1) (ppshow $ toType t2)


-------------------------------------------------------------------------------
subTypeWindTys :: [Location] -> AnnTypeR -> CGEnv -> RefHeap -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeWindTys seen l g σ t1@(TObj _ _) t2@(TObj _ _)
  = do (t1', t2')  <- alignTsM t1 t2 
       -- (t1', g_st) <- freshObjBinds l g t1'
       subTypeContainers l g t1' t2'
       mapM_ (uncurry $ subTypeWindHeaps seen l g σ) $ bkPaddedObject t1 t2
       return ()

subTypeWindTys seen l g σ t1 t2
  = do subTypeContainers l g t1 t2
    
-------------------------------------------------------------------------------
subTypeWindHeaps :: [Location] -> AnnTypeR -> CGEnv -> RefHeap -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeWindHeaps seen l g σ t1@(TApp TUn _ _ _) t2@(TApp TUn _ _ _)
  = do sts <- alignAndStrengthen "subTypeWindHeaps" l g t1 t2 
       mapM_ (uncurry $ subTypeWindHeaps seen l g σ) sts
    
subTypeWindHeaps seen l g σ t1@(TApp (TRef l1) _ _ _) t2@(TApp (TRef l2) _ _ _)
  | l1 /= l2       = error "BUG: Somehow subtyping different locations"
  | not (l2 `heapMem` σ) = return ()
  | l1 `elem` seen = return ()
  | otherwise      = do (x,g') <- envAddFresh l t1 g
                        γ      <- getTDefs
                        let th1 = if heapMem l1 (rheap g') then 
                                    heapReadType g' "st_windHeap 2" l1 (rheap g')
                                  else
                                    expandTApp γ $ rType th2
                            th2 = heapReadType g' "st_windHeap 1" l2 σ 
                        subTypeWind' (l1:seen) l g' σ th1 th2
                        return ()
  -- where 
  --   tru = tTop
  --   fls = tTop `strengthen` F.predReft F.PFalse

subTypeWindHeaps _ _ _ _ _ _ = return ()

---------------------------------------------------------------------------------------
-- | Splitting Well-Formedness Constraints --------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
splitW :: WfC -> CGM [FixWfC]
---------------------------------------------------------------------------------------
splitW (W g i (TFun ts t h h' _)) 
  = do g'     <- envTyAdds i ts g >>= envTyHeapAdds i h
       ws     <- concatMapM splitW [W g' i ti | B _ ti <- ts]
       ws'    <- concatMapM splitW $ W g' i <$> heapTypes (b_type <$> h)
       g''    <- envTyHeapAdds i h' g'
       ws''   <-            splitW (W g'' i (b_type t))
       ws'''  <- concatMapM splitW $ W g'' i <$> heapTypes (b_type <$> h')
       let bws = bsplitW g'' (b_type t) i
       return  $ bws ++ ws ++ ws' ++ ws'' ++ ws'''

splitW (W g i (TAll _ t)) 
  = splitW (W g i t)

splitW (W g i (TAllP _ t)) 
  = splitW (W g i t)

splitW (W g i t@(TVar _ _))
  = return $ bsplitW g t i 

splitW (W g i t@(TApp _ ts rs _))
  =  do let ws = bsplitW g t i
        ws'   <- concatMapM splitW [W g i ti | ti <- ts]
        ws''  <- concatMapM (rsplitW g i) rs
        return $ ws ++ ws' ++ ws''

splitW (W g i t@(TObj ts _ ))
  = do  g'    <- envTyAdds i ts g -- ABAKST Changed!!?!!?
        let bs = bsplitW g t i
        ws    <- concatMapM splitW [W g i ti | B _ ti <- ts]
        return $ bs ++ ws

splitW (W _ _ _ ) = error "Not supported in splitW"

-- rsplitW _ _ (PMono _ _)  = error "PMono in splitW"
rsplitW g i (PPoly xs t)
    =  do g' <- envAdds [ (x, ofType t) | (x,t) <- xs ] g
          splitW $ W g' i t
rsplitW _ _ _ = return [] -- (PMono _ _)  = error "PMono in splitW"

bsplitW g t i 
  | F.isNonTrivialSortedReft r'
  = [F.wfC (fenv g) r' Nothing i] 
  | otherwise
  = []
  where r' = rTypeSortedReft t

-- mkSortedReft tce = F.RR . rTypeSort tce

-- refTypeId ::  (F.Reftable r, IsLocated l) => l -> RType r -> Id l
-- refTypeId l = symbolId l . F.symbol -- rTypeValueVar 

envTyAdds l xts = envAdds [(symbolId l x, t) | B x t <- xts]
envTyHeapAdds l h = envAdds [(symbolId l x, t) | B x t <- heapTypes h]

-------------------------------------------------------------------------------------------

-- | Replace all sorts with FInt


class ClearSorts a where
  clear :: a -> a
  clearM :: a -> CGM a 
  clearM = return . clear

instance ClearSorts F.BindEnv where
  clear = F.mapBindEnv (mapSnd clear)

instance (ClearSorts a, ClearSorts b) => ClearSorts (a,b) where
  clear (a,b) = (clear a, clear b)
                 
instance ClearSorts (F.SubC a) where
  clear (F.SubC e g l r i t ii) = F.SubC e g (clear l) (clear r) i t ii

instance ClearSorts a => ClearSorts [a] where
  clear xs = clear <$> xs

instance ClearSorts F.SortedReft where
  clear (F.RR s r) = F.RR (clear s) r

instance ClearSorts F.Sort where 
  clear F.FInt        = F.FInt
  clear F.FNum        = F.FInt
  clear (F.FObj _)    = F.FInt
  clear v@(F.FVar _)  = v -- F.FInt
  clear (F.FFunc i s) = F.FFunc i $ clear <$> s
  -- clear (F.FApp _ _ ) = F.FInt -- F.FApp  c $ clear s
  clear s@(F.FApp c ss) 
      | F.val (F.fTyconString c) == "set" = F.FApp setSym (clear <$> ss)
      | c == F.propFTyCon         = s
      | c == F.boolFTyCon         = s
      | s == rTypeSort (tBool :: Type) = F.FInt
      | otherwise                 = F.FApp c (clear <$> ss)
      -- | otherwise                 = s 
      -- | otherwise                 = F.FInt -- F.FApp  c $ clear s
  clear s = s
                                    
setSym = F.stringFTycon . F.dummyLoc $ "Set_Set"

clearFunTy s@(F.FVar _) = s
clearFunTy s            = clear s

instance ClearSorts F.Symbol where
  clear = id

instance ClearSorts (F.WfC a) where
  clear (F.WfC e r i ii) = F.WfC e (clear r) i ii 

instance ClearSorts CGInfo where
  clear (CGI f a) = CGI (clear f) a

instance ClearSorts (F.FInfo a) where
  clear (F.FI cm ws bs gs lits kuts quals) =
    {-let msg = printf "\nGS: %s\n\n" (render $ F.toFix $ F.toListSEnv gs) in-}
    F.FI (M.map clear cm)
         (clear ws)
         (clear bs)
         -- XXX: Special treatment for Prop
         (F.mapSEnvWithKey clearProp {- $ trace msg -} gs)
         (clear lits)
         kuts
         quals

clearProp (sy, F.RR so re) 
  | F.symbolString sy == "Prop" 
  = (sy, F.RR (F.FFunc 2 [F.FInt, F.FApp F.boolFTyCon []]) re)
  | otherwise                   
  = (clear sy, clear $ F.RR so re)

envAddFieldBinders l b tObj@(TObj _ _) g
  = do TObj bs _ <- strengthenObjBinds b <$> (true tObj)
       foldM go (g, mempty) bs
  where 
    newSub su x x'    = F.catSubst su $ F.mkSubst [(x, F.eVar x')]
    go (g,su) (B x t) = envAddFresh l t g >>= \(x', g) -> return (g, newSub su x x')

envAddFieldBinders _ _ _ _       = error "BUG: Adding Field Binders NON object!"
