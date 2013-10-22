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
    
  -- * Get Current Function
  , getFun, withFun

  -- * Throw Errors
  , cgError      

  -- * Fresh Templates for Unknown Refinement Types 
  , freshTyFun
  , freshTyInst
  , freshTyPhis
  , freshTyWind
  , freshObjBinds
  , freshHeapEnv

  , strengthenObjBinds

  -- * Freshable
  , Freshable (..)

  -- * Environment API
  , envAddFresh
  , envAdds
  , envAddFreshHeap
  , envFreshHeapBind
  , envAddReturn
  , envAddGuard
  , envFindTy, envFindTy'
  , envFindTyDef
  , envToList
  , envFindReturn
  , envJoin

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

  ) where

import           Data.Maybe                     (fromMaybe)
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


import qualified Language.Fixpoint.Types as F
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
    fixCWs       = (,) <$> fixCs <*> fixWs
    fixCs        = get >>= concatMapM splitC . cs
    fixWs        = get >>= concatMapM splitW . ws

execute :: Config -> Nano AnnTypeR RefType -> CGM a -> (a, CGState)
execute cfg pgm act
  = case runState (runErrorT act) $ initState cfg pgm of 
      (Left err, _) -> errorstar err
      (Right x, st) -> (x, st)  

initState       :: Config -> Nano AnnTypeR RefType -> CGState
initState c pgm = CGS F.emptyBindEnv Nothing (defs pgm) (tDefs pgm) (tMeas pgm) [] [] 0 mempty invs c 
  where 
    invs        = M.fromList [(tc, t) | t@(Loc _ (TApp tc _ _)) <- invts pgm]  

getDefType f 
  = do m <- cg_defs <$> get
       maybe err return $ E.envFindTy f m 
    where 
       err = cgError l $ errorMissingSpec l f
       l   = srcPos f

-- cgStateFInfo :: Nano a1 (RType F.Reft)-> (([F.SubC Cinfo], [F.WfC Cinfo]), CGState) -> CGInfo
cgStateCInfo pgm ((fcs, fws), cg) = CGI (patchSymLits fi) (cg_ann cg)
  where 
    fi   = F.FI { F.cm    = M.fromList $ F.addIds fcs  
                , F.ws    = fws
                , F.bs    = binds cg
                , F.gs    = measureEnv pgm 
                , F.lits  = []
                , F.kuts  = F.ksEmpty
                , F.quals = quals pgm 
                }

patchSymLits fi = fi { F.lits = F.symConstLits fi ++ F.lits fi }
    
---------------------------------------------------------------------------------------
getTDefs :: CGM (E.Env RefType)
---------------------------------------------------------------------------------------
getTDefs  = cg_tdefs <$> get

---------------------------------------------------------------------------------------
getMeasures :: (F.Symbolic s) => s -> CGM [TypeMeasure]             
---------------------------------------------------------------------------------------
getMeasures t = do m <- cg_tmeas <$> get
                   let x = tracePP "Measures:" (M.toList m)
                   return $ M.lookupDefault [] (F.symbol t) m

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


-- | Get binding from object type
-- <<<<<<< HEAD
-- ---------------------------------------------------------------------------------
-- getBinding :: (PP r, F.Reftable r) => E.Env (RType r) -> Id a -> RType r -> Either String (RType r)
-- ---------------------------------------------------------------------------------
-- getBinding _ i (TObj bs _ ) = 
--   case L.find (\s -> F.symbol i == b_sym s) bs of
--     Just b      -> Right $ b_type b
--     _           -> Left  $ errorObjectBinding
-- getBinding defs i t@(TApp (TDef _) _ _) = 
--   case unfoldMaybe defs t of
--     Right (_,t')-> getBinding defs i t'
--     Left  s     -> Left $ s ++ "\nand\n" ++ errorObjectTAccess t
-- getBinding _ _ t = Left $ errorObjectTAccess t
-- =======
-- >>>>>>> pvekris

-- Use the TCMonad dotAccess)


{-----------------------------------------------------------------------------------}
{-getBinding :: (PP r, F.Reftable r, F.Symbolic s) => -}
{-  E.Env (RType r) -> s -> RType r -> Either String (RType r)-}
{-----------------------------------------------------------------------------------}
{-getBinding _ i (TObj bs _ ) = -}
{-  case L.find (\s -> F.symbol i == b_sym s) bs of-}
{-    Just b      -> Right $ b_type b-}
{-    _           -> Left  $ errorObjectBinding-}
{-getBinding defs i t@(TApp (TDef _) _ _) = -}
{-  case unfoldMaybe defs t of-}
{-    Right t'    -> getBinding defs i t'-}
{-    Left  s     -> Left $ s ++ "\nand\n" ++ errorObjectTAccess t-}
{-getBinding _ _ t = Left $ errorObjectTAccess t-}

{-----------------------------------------------------------------------------------------}
{-getBindingM :: (F.Symbolic s) => s -> RefType -> CGM (Either String RefType)-}
{-----------------------------------------------------------------------------------------}
{-getBindingM i t -}
{-  = do  td <- cg_tdefs <$> get-}
{-        return $ getBinding td i t -}


---------------------------------------------------------------------------------------
measureEnv   ::  Nano a (RType F.Reft) -> F.SEnv F.SortedReft
---------------------------------------------------------------------------------------
measureEnv   = fmap rTypeSortedReft . E.envSEnv . consts 

---------------------------------------------------------------------------------------
-- | Constraint Generation Monad ------------------------------------------------------
---------------------------------------------------------------------------------------

data CGState 
  = CGS { binds    :: F.BindEnv            -- ^ global list of fixpoint binders
        , cg_fun   :: !(Maybe F.Symbol)    -- ^ current function
        , cg_defs  :: !(E.Env RefType)     -- ^ type sigs for all defined functions
        , cg_tdefs :: !(E.Env RefType)     -- ^ type definitions
        , cg_tmeas :: !(M.HashMap F.Symbol [TypeMeasure]) -- ^ type measure definitions
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
  = do x  <- tracePP ("envAddFresh " ++ ppshow t) <$> freshId l
       g' <- envAdds [(x, t)] g
       return (x, g')

---------------------------------------------------------------------------------------
envAdds      :: (F.Symbolic x, IsLocated x) => [(x, RefType)] -> CGEnv -> CGM CGEnv
---------------------------------------------------------------------------------------
envAdds xts' g
  = do xts    <- zip xs  <$> mapM addInvariant ts
       is     <- forM xts $  addFixpointBind 
       _      <- forM xts $  \(x, t) -> addAnnot (srcPos x) x t
       return  $ g { renv = E.envAdds xts        (renv g) } 
                   { fenv = F.insertsIBindEnv is (fenv g) }
    where 
       (xs,ts) = unzip xts'

---------------------------------------------------------------------------------------
envAddFreshHeap   :: (IsLocated l) => l -> (Location, RefType) -> CGEnv -> CGM (Id SourceSpan, CGEnv)
---------------------------------------------------------------------------------------
envAddFreshHeap l lt g
  = do x           <- freshId (srcPos l) 
       g'          <- envAdds [(x, snd lt)] g
       return $ (x, g' { rheap = heapCombineWith const [heapBinders [(fst lt, x)] , rheap g'] })
  where heapBinders = heapFromBinds "envAddHeap" 

envFreshHeapBind :: (IsLocated l) => l -> Location -> CGEnv -> CGM (Id SourceSpan, CGEnv)
envFreshHeapBind l j g
  = freshId (srcPos l) >>= (\i -> return $ (i, g { rheap = newHeap i }))
    where
      newHeap i   = heapCombineWith const [heapBinders [(j,i)], rheap g]
      heapBinders = heapFromBinds "envAddHeap" 

addFixpointBind :: (F.Symbolic x) => (x, RefType) -> CGM F.BindId
addFixpointBind (x, t) 
  = do let s     = F.symbol x
       let r     = rTypeSortedReft t
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
    tx i t@(TApp tc _ _)   = maybe t (strengthen t . rTypeReft . val) $ M.lookup (fixRef tc) i
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
envFindTyDef  :: Id SourceSpan -> CGM (RHeapEnv F.Reft, F.Symbol, RefType, [TVar])
---------------------------------------------------------------------------------------
envFindTyDef ty
  = do γ <- getTDefs
       case E.envFindTy ty γ of
         Just (TBd t) -> 
           return (td_heap t, td_self t, td_body t, td_args t)
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
  = do let (σ1,σ2)        = mapPair rheap (g1,g2)
           (one,both,two) = heapSplit σ1 σ2
           t1s            = map (snd . safeRefReadHeap "joinHeaps" g1 σ1) both
           t2s            = map (snd . safeRefReadHeap "joinHeaps" g2 σ2) both
           t4             = zipWith (compareTs γ) t1s t2s
       ts                <- mapM (freshTy "joinHeaps" . toType . fst4) t4
       xs                <- mapM (const (freshId (srcPos l))) ts
       g'                <- envAdds (zipWith str xs ts) g
       _                 <- mapM (wellFormed l g') ts
       let σ'             = heapCombine "joinHeaps combine " [σj, σ2', σ1']
           σ1'            = heapFromBinds "joinHeaps one" $ zip one $ map (fst . safeRefReadHeap "joinHeaps one" g1 σ1) one
           σ2'            = heapFromBinds "joinHeaps two" $ zip two $ map (fst . safeRefReadHeap "joinHeaps two" g2 σ2) two
           σj             = tracePP "joinHeaps joined" $ heapFromBinds "joinHeaps σj" $ zip both xs
           su1            = F.mkSubst $ zip (F.symbol <$> xs) (map (F.eVar . F.symbol . flip (heapRead "joinHeaps") σ1) both)
           su2            = F.mkSubst $ zip (F.symbol <$> xs) (map (F.eVar . F.symbol . flip (heapRead "joinHeaps") σ2) both)
       -- Subtype the common heap locations
       zipWithM_ (subTypeContainers l g1) (tracePP "snd4 t4" $ map snd4 t4) (map (F.subst su1 <$>) ts)
       zipWithM_ (subTypeContainers l g2) (map thd4 t4) (map (F.subst su2 <$>) ts)
       (ts',g')        <- foldM foldFresh ([],g') (map (flip envFindTy g') xs)
       xs'             <- mapM (const (freshId (srcPos l))) xs
       g''             <- envAdds (zip xs' (reverse ts')) g'
       return $ g'' { rheap = σ' }
    where
      foldFresh (ts,g) t = freshObjBinds l g t >>= \(t',g') -> return (t':ts, g')
      str x t  = (x, strengthenObjBinds x t)
           
---------------------------------------------------------------------------------------
-- | Fresh Templates ------------------------------------------------------------------
---------------------------------------------------------------------------------------
       
-- | Instantiate Fresh Type (at Function-site)
---------------------------------------------------------------------------------------
freshTyFun :: (IsLocated l) => CGEnv -> l -> Id AnnTypeR -> RefType -> CGM RefType 
---------------------------------------------------------------------------------------
freshTyFun g l f t = freshTyFun' g l f t . kVarInst . cg_opts =<< get  

freshTyFun' g l _ t b
  | b && isTrivialRefType t = freshTy "freshTyFun" (toType t) >>= \t -> wellFormed l g t
  | otherwise               = return t

-- | Instantiate Fresh Type (at Call-site)

---------------------------------------------------------------------------------------
-- freshTyInst :: (IsLocated l) => l -> CGEnv -> [TVar] -> [Type] -> RefType -> CGM RefType 
-- freshTyInst :: AnnTypeR -> CGEnv -> [TVar] -> [Type] -> RefType -> CGM RefType 
---------------------------------------------------------------------------------------
freshTyInst l g αs τs tbody
  = do ts    <- mapM (freshTy "freshTyInst") τs
       _     <- mapM (wellFormed l g) ts
       let θ  = fromLists (zip αs ts) []
       return $ tracePP msg $  apply θ tbody
    where
       msg = printf "freshTyInst αs=%s τs=%s: " (ppshow αs) (ppshow τs)

-- | Instantiate Fresh Type (at Wind-site)
--------------------------------------------------------------------------------------
freshTyWind :: (PP l, IsLocated l) => 
               CGEnv -> l -> RSubst F.Reft -> Id SourceSpan 
               -> CGM ((RefHeap, (F.Symbol, RefType), RefType, [TypeMeasure]), CGEnv)
---------------------------------------------------------------------------------------
freshTyWind g l θ ty
  = do (σ,s,t,vs)    <- envFindTyDef ty
       let (αs,ls)  = toLists θ
       αs'         <- mapM freshSubst αs
       let θ'       = fromLists αs' ls
       (su,σ')     <- freshHeapEnv l (apply (tracePP "freshTyWind inst" θ') $ tracePP "freshTyWind sig" σ)
       ms          <- (instMeas su <$>) <$> getMeasures (tracePP "freshTyWind" ty)
       g'          <- envAdds (toIdTyPair <$> heapTypes σ') g
       return ((tracePP "freshTyWind sig out" (toId <$> σ'), (s,F.subst su $ apply θ' t), mkApp (apply θ' . tVar <$> vs), ms), g')
    where 
      instMeas su (id, sym, e) = (id, sym, F.subst su e)
      s                    = srcPos l
      toId                 = Id s . F.symbolString . b_sym                      
      toIdTyPair b         = (toId b, b_type b)
      -- instHeapBind θ (m,b) = error "TBD: freshTyWind" >> {- freshBind l b >>= -} \b -> return (apply θ m, b)
      mkApp vs             = TApp (TDef ty) vs F.top
      freshSubst (α,τ)     = do τ <- freshTy "freshTyWind" τ
                                _ <- wellFormed l g τ
                                return (α,τ)

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
---------------------------------------------------------------------------------------
freshObjBinds :: (PP l, IsLocated l) => l -> CGEnv -> RefType -> CGM (RefType, CGEnv)
---------------------------------------------------------------------------------------
freshObjBinds l g (TObj bs r)
  = do let xs  = b_sym <$> bs
       xs'     <- mapM (const (freshId l)) bs
       g'      <- envAdds (safeZip "freshObjBinds" xs' (b_type <$> bs)) g
       let bs' = safeZip "freshOBjBinds'" xs $ map (flip envFindTy g') xs'
       return (TObj [ B (F.symbol x) t | (x,t) <- bs' ] r, g')

freshObjBinds _ g t
  = return (t, g)

---------------------------------------------------------------------------------------
freshHeapEnv :: (PP l, IsLocated l) => l -> RHeapEnv F.Reft -> CGM (F.Subst, RHeapEnv F.Reft)
---------------------------------------------------------------------------------------
freshHeapEnv l σ
  = do let xs  = b_sym <$> heapTypes σ
       xs'     <- mapM (const (freshId (srcPos l))) xs
       let su  = F.mkSubst $ zip (F.symbol <$> xs) (F.eVar . F.symbol <$> xs')
       return $ (su, heapBind . zipUp (replace su) xs' $ heapBinds σ)
    where
      heapBind                 = heapFromBinds "freshHeapEnv"
      zipUp                    = safeZipWith "freshHeapEnv"
      replace su x' (l, B x t) = (l, B (F.symbol x') (F.subst su t))


strengthenObjBinds x (TObj bs r)
  = TObj (f <$> bs) r
  where
    f (B b t) = B b $ eSingleton t (field x b)

strengthenObjBinds _ t = t

-- loc |-> x, x.f := y
updateFieldM :: (IsLocated l, F.Symbolic f) => l -> CGEnv -> Id SourceSpan -> Id SourceSpan -> f -> Id l -> CGM (RefType, CGEnv)
updateFieldM l g x x' f y
  = do let t_obj       = tracePP "t_obj" $ envFindTy x g
           t_fld       = tracePP "deref" $ deref x' (envFindTy y g) s
       (y', g') <- envAddFresh l t_fld g
       return $ (tracePP "updateField" $ updateField (envFindTy y' g') s t_obj, g')
    where   
      s           = F.symbol f
      deref x t b = t `eSingleton` (field x b)


-- HACK
field x y = F.EApp (F.symbol "field") [F.expr $ F.symbol x, bind2sym y]
  where bind2sym = F.ESym . F.SL . F.symbolString

  
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
subTypeHeaps :: AnnTypeR -> CGEnv -> Heap RefType -> Heap RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeHeaps l g σ1 σ2 = 
  do let (_,ls,_) = heapSplit σ1 σ2
     mapM_ subTypeLoc ls
         -- t1s      = map (safeRefReadHeap "subTypeHeaps" g σ1) ls
         -- t2s      = map (safeRefReadHeap "subTypeHeaps" g σ2) ls
     -- mapM_ (subTypeField l g) (zip t1s t2s)
  where 
    subTypeLoc loc = subTypeField l g (heapRead "subTypeHeaps(a)" loc σ1) (heapRead "subTypeHeaps(b)" loc σ2)
    
subTypeField l g = withAlignedM doSubType
  where doSubType t1 t2 = do subTypeContainers' "subTypeField" l g t1 t2 
                             subType' "subTypeField" l g t1 t2
  -- do γ <- getTDefs
     -- case tracePP "subTypeField" $ fth4 $ compareTs γ t1 t2 of
     --   Nth -> subTypeContainers' "dead" l g tTop (tTop `strengthen` F.predReft F.PFalse)
     --   _   -> withAlignedM (subTypeContainers l g) t1 t2

         
  

-------------------------------------------------------------------------------
equivWUnions :: E.Env RefType -> RefType -> RefType -> Bool
-------------------------------------------------------------------------------
equivWUnions γ t1@(TApp TUn _ _) t2@(TApp TUn _ _) = 
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
subTypeContainers :: AnnTypeR -> CGEnv -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeContainers l g (TApp d@(TDef _) ts _) (TApp d'@(TDef _) ts' _) | d == d' = 
  mapM_ (uncurry $ subTypeContainers' "def0" l g) $ zip ts ts'

subTypeContainers l g t1 t2@(TApp (TDef _) _ _ ) = 
  unfoldSafeCG t2 >>= \t2' -> subTypeContainers' "subc def1" l g t1 t2'

subTypeContainers l g t1@(TApp (TDef _) _ _ ) t2 = 
  unfoldSafeCG t1 >>= \t1' -> subTypeContainers' "subc def2" l g t1' t2

subTypeContainers l g u1@(TApp TUn _ _) u2@(TApp TUn _ _) = 
  getTDefs >>= \γ -> sbs $ bkPaddedUnion "subTypeContainers" γ u1 u2
  where        
    (r1, r2)     = mapPair rTypeR        (u1, u2)
    -- Fix the ValueVar of the top-level refinement to be the same as the
    -- Valuevar of the part
    fix t b v    | v == b    = rTypeValueVar t
                 | otherwise = v
    rr t r       = F.substa (fix t b) r where F.Reft (b,_) = r
    sb  (t1 ,t2) = subTypeContainers' "subc un" l g (t1 `strengthen` rr t1 r1) 
                                         (t2 `strengthen` rr t2 r2)
    sbs ts       = mapM_ sb ts

-- TODO: the environment for subtyping each part of the object should have the
-- tyopes for the rest of the bindings
subTypeContainers l g o1@(TObj _ _) o2@(TObj _ _) = 
  getTDefs >>= \γ -> sbs $ bkPaddedObject o1 o2
  where
    sbs          = mapM_ sb
    (r1, r2)     = mapPair rTypeR (o1, o2)
    -- Fix the ValueVar of the top-level refinement 
    -- to be the same as the Valuevar of the part
    fix t b v    | v == b    = rTypeValueVar t
                 | otherwise = v
    rr t r       = F.substa (fix t b) r where F.Reft (b,_) = r
    sb (t1 ,t2)  = subTypeContainers' "subc obj" l g (t1 `strengthen` rr t1 r1) 
                                         (t2 `strengthen` rr t2 r2)

subTypeContainers l g t1 t2 = subType l g t1 t2


subTypeContainers' msg l g t1 t2 = 
  subTypeContainers l g (tracePP (printf "subTypeContainers[%s]:\n\t%s\n\t%s" 
                                msg (ppshow t1) (ppshow t2)) t1) t2

alignAndStrengthen msg l g u1@(TApp TUn _ _) u2@(TApp TUn _ _) =
  getTDefs >>= return . (\γ -> bkPaddedUnion msg γ u1' u2')
  -- getTDefs >>= return . (\γ -> map fixup $ bkPaddedUnion msg γ u1 u2)
  where 
    (u1',u2') = mapPair strengthenUnion (u1,u2)
  -- where
  --   (r1, r2)       = mapPair rTypeR (u1, u2)
  --   fix t b v 
  --     | v == b     = rTypeValueVar t
  --     | otherwise  = v
  --   rr t r         = F.substa (fix t b) r where F.Reft (b,_) = r
  --   fixup (t1, t2) = (t1 `strengthen` rr t1 r1, t2 `strengthen` rr t2 r2)
 
alignAndStrengthen msg l g t1 t2 = return [(t1, t2)]

------------------------------------------------------------------------------------------
strengthenUnion :: RefType -> RefType
------------------------------------------------------------------------------------------
strengthenUnion (TApp TUn ts r) = TApp TUn (map fixup ts) r
  where fix t b v
          | v == b    = rTypeValueVar t
          | otherwise = v
        rr t r  = F.substa (fix t b) r where F.Reft (b,_) = r
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
  fresh = F.tempSymbol "nano" <$> fresh

instance Freshable String where
  fresh = F.symbolString <$> fresh

freshId   :: (IsLocated l) => l -> CGM (Id l)
freshId l = Id l <$> fresh

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

instance Freshable F.SortedReft where
  fresh                  = errorstar "fresh Reft"
  true    (F.RR so r)    = F.RR so <$> true r 
  refresh (F.RR so r)    = F.RR so <$> refresh r

instance Freshable RefType where
  fresh   = errorstar "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType 

trueRefType    :: RefType -> CGM RefType
trueRefType    = mapReftM true

refreshRefType :: RefType -> CGM RefType
refreshRefType = mapReftM refresh

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
splitC' (Sub g i tf1@(TFun xt1s t1 _ _ _) tf2@(TFun xt2s t2 _ _ _))
  = do let bcs    = bsplitC g i tf1 tf2
       g'        <- envTyAdds i xt2s g 
       cs        <- concatMapM splitC $ safeZipWith "splitC1" (Sub g' i) t2s t1s' 
       cs'       <- splitC $ Sub g' i (F.subst su t1) t2      
       return     $ bcs ++ cs ++ cs'
    where 
       t2s        = b_type <$> xt2s
       t1s'       = F.subst su (b_type <$> xt1s)
       su         = F.mkSubst $ safeZipWith "splitC2" bSub xt1s xt2s
       bSub b1 b2 = (b_sym b1, F.eVar $ b_sym b2)

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
splitC' (Sub g i t1@(TApp TUn _ _) t2@(TApp TUn _ _)) =
  ifM (equivWUnionsM t1 t2) 
    (return    $ bsplitC g i t1 t2) 
    (errorstar $ printf "Unequal unions in splitC: %s - %s" (ppshow $ toType t1) (ppshow $ toType t2))

splitC' (Sub _ _ t1@(TApp TUn _ _) t2) = 
  errorstar $ printf "Unions in splitC: %s - %s" (ppshow t1) (ppshow t2)
splitC' (Sub _ _ t1 t2@(TApp TUn _ _)) = 
  errorstar $ printf "Unions in splitC: %s - %s" (ppshow t1) (ppshow t2)

---------------------------------------------------------------------------------------
-- |Type definitions
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TApp d1@(TDef _) t1s _) t2@(TApp d2@(TDef _) t2s _)) | d1 == d2
  = do  let cs = bsplitC g i t1 t2
        -- constructor parameters are covariant
        cs'   <- concatMapM splitC $ safeZipWith "splitcTDef" (Sub g i) t1s t2s
        return $ cs ++ cs' 

splitC' (Sub _ _ (TApp (TDef _) _ _) (TApp (TDef _) _ _))
  = errorstar "Unimplemented: Check type definition cycles"
  
splitC' (Sub g i t1@(TApp (TDef _) _ _ ) t2) = 
  unfoldSafeCG t1 >>= \t1' -> splitC' $ Sub g i t1' t2

splitC' (Sub g i  t1 t2@(TApp (TDef _) _ _)) = 
  unfoldSafeCG t2 >>= \t2' -> splitC' $ Sub g i t1 t2'

---------------------------------------------------------------------------------------
-- | Rest of TApp
---------------------------------------------------------------------------------------
splitC' (Sub g i t1@(TApp _ t1s _) t2@(TApp _ t2s _))
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


---------------------------------------------------------------------------------------
bsplitC :: (F.Reftable r) => CGEnv -> a -> RType r -> RType r -> [F.SubC a]
---------------------------------------------------------------------------------------
bsplitC g ci t1 t2
  | F.isFunctionSortedReft r1 && F.isNonTrivialSortedReft r2
  = [F.subC (fenv g) F.PTrue (r1 {F.sr_reft = F.top}) r2 Nothing [] ci]
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
       subTypeContainers' "WeakUpdate" l g' tobj  t
       subTypeContainers' "WeakUpdate" l g' tobj' t
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

subTypeWind' seen l g σ t1 t2 = tracePP msg () `seq` withAlignedM (subTypeWindTys seen l g σ) t1 t2
  where
    msg = printf "subTypeWind %s/%s <: %s/%s" 
          (ppshow $ toType t1) (ppshow (rheap g)) (ppshow $ toType t2) (ppshow σ)


-------------------------------------------------------------------------------
subTypeWindTys :: [Location] -> AnnTypeR -> CGEnv -> RefHeap -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeWindTys seen l g σ t1@(TObj _ _) t2@(TObj _ _)
  = do (t1', t2') <- alignTsM t1 t2 
       subTypeContainers' "Wind" l g (tracePP "subTypeWindTys" t1') (tracePP "subTypeWindTys" t2')
       mapM_ (uncurry $ subTypeWindHeaps seen l g σ) $ bkPaddedObject t1 t2

subTypeWindTys seen l g σ t1 t2
  = subTypeContainers' "Wind Non-Obj" l g t1 t2
    
-- renameLocations :: CGEnv -> RefHeap -> RefType -> RefType -> CGM (RSubst F.Reft)
-- renameLocations g σ t1 t2 
--   = do γ              <- getTDefs
--        let envLocs     = concat [ locs t | (Id _ s,t) <- envToList g
--                                          , F.symbol s /= returnSymbol ]
--                          ++ heapLocs (rheap g)
--            ls          = filter (okRename (tracePP "envLocs" envLocs) σ) $ tracePP "rename" $ rename γ t1 t2
--        return $ fromLists [] ls
--     where
--       okRename locs σ (l2,l1) = l2 `notElem` locs && l1 `notElem` heapLocs σ
--       rename γ t1 t2          = case unify γ mempty t1 t2 of
--                                   Left msg -> error msg
--                                   Right θ  -> snd $ toLists θ
    
-------------------------------------------------------------------------------
subTypeWindHeaps :: [Location] -> AnnTypeR -> CGEnv -> RefHeap -> RefType -> RefType -> CGM ()
-------------------------------------------------------------------------------
subTypeWindHeaps seen l g σ t1@(TApp TUn _ _) t2@(TApp TUn _ _)
  = do sts <- alignAndStrengthen "subTypeWindHeaps" l g t1 t2 
       mapM_ (uncurry $ subTypeWindHeaps seen l g σ) sts
    
subTypeWindHeaps seen l g σ t1@(TApp (TRef l1) _ _) t2@(TApp (TRef l2) _ _)
  | l1 /= l2       = error "BUG: Somehow subtyping different locations"
  | not (l2 `heapMem` σ) = return ()
    -- subTypeContainers' "dead" l g tru fls
  | l1 `elem` seen = return ()
  | otherwise      = do (x,g') <- envAddFresh l t1 g
                        let th2 = snd $ safeRefReadHeap "subTypeWindHeaps(a)" g σ l2
                            th1 = if heapMem l1 (rheap g') then 
                                    snd $ safeRefReadHeap "subTypeWindHeaps(b)" g (rheap g') l1
                                  else
                                    rType th2
                        subTypeWind' (l1:seen) l g' σ th1 th2
                        return ()
  where 
    tru = tTop
    fls = tTop `strengthen` F.predReft F.PFalse

subTypeWindHeaps _ _ _ _ _ _ = return ()

---------------------------------------------------------------------------------------
-- | Splitting Well-Formedness Constraints --------------------------------------------
---------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------
splitW :: WfC -> CGM [FixWfC]
---------------------------------------------------------------------------------------
splitW (W g i (TFun ts t h h' _)) 
  = do let bws = bsplitW g t i
       g'     <- envTyAdds i ts g 
       ws     <- concatMapM splitW [W g' i ti | B _ ti <- ts]
       ws'    <-            splitW (W g' i t)
       ws''   <- concatMapM splitW $ W g' i <$> heapTypes (b_type <$> h)
       ws'''  <- concatMapM splitW $ W g' i <$> heapTypes (b_type <$> h')
       return  $ bws ++ ws ++ ws' ++ ws'' ++ ws'''

splitW (W g i (TAll _ t)) 
  = splitW (W g i t)

splitW (W g i t@(TVar _ _))
  = return $ bsplitW g t i 

splitW (W g i t@(TApp _ ts _))
  =  do let ws = bsplitW g t i
        ws'   <- concatMapM splitW [W g i ti | ti <- ts]
        return $ ws ++ ws'

splitW (W g i t@(TObj ts _ ))
  = do  g'    <- envTyAdds i ts g
        let bs = bsplitW g t i
        ws    <- concatMapM splitW [W g' i ti | B _ ti <- ts]
        return $ bs ++ ws

splitW (W _ _ _ ) = error "Not supported in splitW"

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
  clear (F.FVar _)    = F.FInt
  clear (F.FFunc i s) = F.FFunc i $ clear <$> s
  clear (F.FApp _ _ ) = F.FInt -- F.FApp  c $ clear s

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
