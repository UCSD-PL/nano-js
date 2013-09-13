{- LANGUAGE TypeSynonymInstances      #-}
{- LANGUAGE FlexibleInstances         #-}
{- LANGUAGE NoMonomorphismRestriction #-}
{- LANGUAGE ScopedTypeVariables       #-}

-- | This module has the code for the Type-Checker Monad. 

module Language.Nano.Typecheck.TCMonad (
  -- * TC Monad
    TCM
 
  -- * Execute 
  , execute

  -- * Log Errors
  , logError
  
  -- * Error Action
  , tcError

  -- * Freshness
  , freshTyArgs
  , freshLocation
  , freshSubst
  , freshHeap
  , freshHeapVar
  , tick

  -- * Dot Access
  , dotAccess
  , dotAccessRef

  -- * Type definitions
  , getTDefs

  -- * Substitutions
  , getSubst, setSubst
  , safeHeapSubstM
  , safeHeapSubstWithM

  -- * Functions
  , getFun, setFun

  -- * Annotations
  , accumAnn
  , getAllAnns

  -- * Unfolding
  , unfoldFirstTC
  , unfoldSafeTC
  , unwindTC
  , recordWindExpr
  , recordUnwindExpr
  , getUnwound
  , setUnwound
  , withUnwound
  , pushUnwound

  -- * Subtyping
  , subTypeM  , subTypeM'
  , subTypesM , subHeapM

  -- * Unification
  , unifyTypeM, unifyTypesM
  , unifyHeapsM

  -- * Casts
  , getCasts, getHCasts
  , castM, castsM, castHeapM
  
  -- * Get Type Signature 
  , getDefType 

    -- * Expression Getter/Setter
  , getExpr, setExpr, withExpr

  -- * Patch the program with assertions
  , patchPgmM

  -- * Verbosity
  , whenLoud', whenLoud
  , whenQuiet', whenQuiet

  )  where 

import           Text.Printf
import           Control.Applicative            ((<$>))
import           Control.Monad.State
import           Control.Monad.Error
import           Language.Fixpoint.Misc 
import qualified Language.Fixpoint.Types as F

import           Language.Nano.Env
import           Language.Nano.Misc             (unique, everywhereM', zipWith3M_)
import           Language.Nano.Types
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Unify
import           Language.Nano.Errors
import           Data.Monoid                  
import qualified Data.HashMap.Strict            as HM
import qualified Data.Map                       as M
import           Data.Generics                  (Data(..))
import           Data.Maybe                     (fromJust)
import           Data.List                      (find, partition, nub, sort, unzip4)
import           Data.Generics.Aliases
import           Data.Typeable                  (Typeable (..))
import           Language.ECMAScript3.Parser    (SourceSpan (..))
-- import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations

import           Text.Parsec.Pos

-- import           Debug.Trace                      (trace)
import qualified System.Console.CmdArgs.Verbosity as V

-------------------------------------------------------------------------------
-- | Typechecking monad -------------------------------------------------------
-------------------------------------------------------------------------------

data TCState = TCS { 
                   -- Errors
                     tc_errss    :: ![(SourceSpan, String)]
                   , tc_subst    :: !Subst
                   , tc_cnt      :: !Int
                   -- Annotations
                   , tc_anns     :: AnnInfo
                   , tc_annss    :: [AnnInfo]
                   -- Heap bookkeeping
                   , tc_unwound  :: [(Location, Id SourceSpan)] 
                   , tc_winds    :: M.Map SourceSpan [WindCall]
                   , tc_unwinds  :: M.Map SourceSpan [(Location, Id SourceSpan)]
                   -- Cast map: 
                   , tc_casts    :: M.Map (Expression AnnSSA) (Cast Type)
                   , tc_hcasts   :: M.Map (Expression AnnSSA) (Cast (Heap Type))
                   -- Function definitions
                   , tc_defs     :: !(Env Type) 
                   , tc_fun      :: !(Maybe F.Symbol)
                   -- Type definitions
                   , tc_tdefs    :: !(Env Type)
                   -- The currently typed expression 
                   , tc_expr     :: Maybe (Expression AnnSSA)

                   -- Verbosiry
                   , tc_verb  :: V.Verbosity
                   }

type TCM     = ErrorT String (State TCState)
type WindCall = (Location, Id SourceSpan, Expression AnnSSA, Expression AnnSSA)

-------------------------------------------------------------------------------
whenLoud :: TCM () -> TCM ()
-------------------------------------------------------------------------------
whenLoud  act = whenLoud' act $ return ()

-------------------------------------------------------------------------------
whenLoud' :: TCM a -> TCM a -> TCM a
-------------------------------------------------------------------------------
whenLoud' loud other = do  v <- tc_verb <$> get
                           case v of
                             V.Loud -> loud 
                             _      -> other

-------------------------------------------------------------------------------
whenQuiet :: TCM () -> TCM ()
-------------------------------------------------------------------------------
whenQuiet  act = whenQuiet' act $ return ()

-------------------------------------------------------------------------------
whenQuiet' :: TCM a -> TCM a -> TCM a
-------------------------------------------------------------------------------
whenQuiet' quiet other = do  v <- tc_verb <$> get
                             case v of
                               V.Quiet -> quiet
                               _       -> other

-------------------------------------------------------------------------------
getTDefs :: TCM (Env Type)
-------------------------------------------------------------------------------
getTDefs = tc_tdefs <$> get 

-------------------------------------------------------------------------------
getSubst :: TCM Subst
-------------------------------------------------------------------------------
getSubst = tc_subst <$> get 

-- getCasts :: TCM (M.Map (Expression AnnSSA) Type)
getCasts = getCastsF tc_casts

getHCasts = getCastsF tc_hcasts

getCastsF f = do c <- f <$> get
                 return $ M.toList c

-------------------------------------------------------------------------------
setSubst   :: Subst -> TCM () 
-------------------------------------------------------------------------------
setSubst θ = modify $ \st -> st { tc_subst = θ }


-------------------------------------------------------------------------------
getFun     :: TCM (Maybe F.Symbol)
-------------------------------------------------------------------------------
getFun   = tc_fun <$> get

-------------------------------------------------------------------------------
setFun     :: F.Symbol -> TCM ()
-------------------------------------------------------------------------------
setFun f = modify $ \st -> st { tc_fun = Just f }

-------------------------------------------------------------------------------
extSubst :: [TVar] -> TCM ()
-------------------------------------------------------------------------------
extSubst βs = getSubst >>= setSubst . (`mappend` θ')
  where 
    θ'      = fromList $ zip βs (tVar <$> βs)


-------------------------------------------------------------------------------
tcError :: (IsLocated l) => l -> String -> TCM a
-------------------------------------------------------------------------------
tcError l msg = throwError $ printf "TC-ERROR at %s : %s" (ppshow $ srcPos l) msg


-------------------------------------------------------------------------------
logError   :: SourceSpan -> String -> a -> TCM a
-------------------------------------------------------------------------------
logError l msg x = (modify $ \st -> st { tc_errss = (l,msg):(tc_errss st)}) >> return x


-------------------------------------------------------------------------------
freshTyArgs :: SourceSpan -> ([TVar], Type) -> TCM Type 
-------------------------------------------------------------------------------
freshTyArgs l (αs, t) 
  = (`apply` t) <$> freshSubst l αs

freshSubst :: SourceSpan -> [TVar] -> TCM Subst
freshSubst l αs
  = do
      fUnique αs
      βs        <- mapM (freshTVar l) αs
      setTyArgs l βs
      extSubst βs 
      return     $ fromList $ zip αs (tVar <$> βs)
    where
      fUnique xs = when (not $ unique xs) $ logError l errorUniqueTypeParams ()

setTyArgs l βs 
  = do m <- tc_anns <$> get 
  --      when (HM.member l m) $ tcError l "Multiple Type Args"
       addAnn l $ TypInst (tVar <$> βs)


-------------------------------------------------------------------------------
-- | Field access -------------------------------------------------------------
-------------------------------------------------------------------------------

-- Returns a result type, a list of locations that have been unwound, 
-- and possibly a (fresh) heap that might have been unwound     
-------------------------------------------------------------------------------
dotAccessRef :: BHeap -> Id AnnSSA -> Type -> TCM (Maybe (Type, Type, [(Location,Type)], BHeap))
-------------------------------------------------------------------------------
dotAccessRef _ _ (TApp TNull _ _) = return Nothing

dotAccessRef σ f ref@(TApp (TRef l) _ _) = do 
  r <- dotAccess f (heapRead l σ)
  case r of 
    Just (t, Just tuw,  Just σ') -> do
         -- If something was unwound, the type
         -- at l must have been an application
         addUnwound (l, defAtLoc σ l)
         return $ Just (ref, t, [(l, tuw)], σ')
    Just (t, Nothing,  Nothing) -> return $ Just (ref, t, [], heapEmpty)
    _                           -> return Nothing

dotAccessRef σ f (TApp TUn ts _)     = do 
  e   <- fromJust <$> getExpr
  tfs <- mapM (dotAccessRef σ f) ts
  let (ts', tfs') = unzip [(t,tf) | (t, Just tf) <- zip ts tfs]
  castM e (mkUnion ts) (mkUnion ts')
  case tfs' of
    [] -> return Nothing
    ps -> let (refs, rs, uwts, σs) = unzip4 ps 
          in return $ Just (mkUnion refs, mkUnion rs, concat uwts, heapCombine σs)

dotAccessRef _ _ t  = error $ "Can not dereference " ++ (ppshow t)

defAtLoc σ l = go $ heapRead l σ                      
  where go (TApp (TDef i) _ _) = i
        go t                   = error $ "BUG: Somehow unwound " ++ (ppshow t)

-------------------------------------------------------------------------------
dotAccess :: Id AnnSSA -> Type -> TCM (Maybe (Type, Maybe Type, Maybe BHeap))
-------------------------------------------------------------------------------
dotAccess f   t@(TObj bs _) = 
  return $ Just (maybe tUndef b_type $ find (match $ F.symbol f) bs, Nothing, Nothing)
  where match s (B f _)  = s == f

dotAccess f t@(TApp c ts _ ) = go c
  where  go TUn      = dotAccessUnion f ts
         go TInt     = return $ Just (tUndef, Nothing, Nothing)
         go TBool    = return $ Just (tUndef, Nothing, Nothing)
         go TString  = return $ Just (tUndef, Nothing, Nothing)
         go TUndef   = return   Nothing
         go TNull    = return   Nothing
         go (TDef _) = dotAccessDef f t
         go TTop     = error "dotAccess top"
         go TVoid    = error "dotAccess void"
         go (TRef _)  = error "dotAccess ref"

dotAccess _   t@(TFun _ _ _ _ _ ) = return $ Just (tUndef, Nothing, Nothing)
dotAccess _ t               = error $ "dotAccess " ++ (ppshow t) 

dotAccessDef :: Id AnnSSA -> Type -> TCM (Maybe (Type, Maybe Type, Maybe BHeap))
dotAccessDef f t = do 
  (σ,t')    <- unwindTC t
  (θ',_,σ') <- freshHeap σ
  da        <- dotAccess f $ apply θ' t'
  case da of
    Just (t,  Nothing, Nothing)  -> return $ Just (apply θ' t, Just $ apply θ' t', Just σ')
    -- Do the next two even make sense?
    -- Just (t, Just t'', Just σ'') -> return $ Just (t, Just t'', Just $ heapCombine[σ',σ''])
    -- Just (t, Just t'', Nothing)  -> return $ Just (t, Just t'', Just σ')
    _                            -> return da


-------------------------------------------------------------------------------
dotAccessUnion :: Id AnnSSA -> [Type] -> TCM (Maybe (Type, Maybe Type, Maybe BHeap))
-------------------------------------------------------------------------------
dotAccessUnion f ts = 
  do  e              <- fromJust <$> getExpr
      tfs            <- mapM (dotAccess f) ts
      -- Gather all the types that do not throw errors, and the type of 
      -- the accessed expression that yields them
      let (ts', tfs') = unzip [(t,tf) | (t, Just tf) <- zip ts tfs]
      castM e (mkUnion ts) (mkUnion ts')
      case tfs' of
        [] -> return Nothing
        ps -> let (rs, ts, σs) = unzip3 ps 
                  mt           = return $ mkUnion [t | Just t <- ts]
                  mσ           = return $ heapCombine [σ | Just σ <- σs]
              in return $ Just (mkUnion rs, mt, mσ)
  
      

-------------------------------------------------------------------------------
-- | Managing Annotations: Type Instantiations --------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
getAnns :: TCM AnnInfo  
-------------------------------------------------------------------------------
getAnns = do θ     <- tc_subst <$> get
             m     <- tc_anns  <$> get
             let m' = fmap (apply θ . sortNub) m
             _     <- modify $ \st -> st { tc_anns = m' }
             return m' 

-------------------------------------------------------------------------------
addAnn :: SourceSpan -> Fact -> TCM () 
-------------------------------------------------------------------------------
addAnn l f = modify $ \st -> st { tc_anns = inserts l f (tc_anns st) } 

-------------------------------------------------------------------------------
getAllAnns :: TCM [AnnInfo]  
-------------------------------------------------------------------------------
getAllAnns = tc_annss <$> get


-------------------------------------------------------------------------------
accumAnn :: (AnnInfo -> [(SourceSpan, String)]) -> TCM () -> TCM ()
-------------------------------------------------------------------------------
accumAnn check act 
  = do m     <- tc_anns <$> get 
       modify $ \st -> st {tc_anns = HM.empty}
       act
       m'    <- getAnns
       forM_ (check m') $ \(l, s) -> logError l s ()
       modify $ \st -> st {tc_anns = m} {tc_annss = m' : tc_annss st}

-------------------------------------------------------------------------------
execute     :: V.Verbosity -> Nano z (RType r) -> TCM a -> Either [(SourceSpan, String)] a
-------------------------------------------------------------------------------
execute verb pgm act 
  = case runState (runErrorT act) $ initState verb pgm of 
      (Left err, _) -> Left [(dummySpan,  err)]
      (Right x, st) ->  applyNonNull (Right x) Left (reverse $ tc_errss st)


initState :: V.Verbosity -> Nano z (RType r) -> TCState
initState verb pgm = TCS tc_errss tc_subst tc_cnt tc_anns tc_annss tc_unwound tc_winds tc_unwinds
                       tc_casts tc_hcasts tc_defs tc_fun tc_tdefs tc_expr tc_verb 
  where
    tc_errss    = []
    tc_subst    = mempty 
    tc_cnt      = 0
    tc_anns     = HM.empty
    tc_annss    = []
    tc_unwound  = []
    tc_winds    = M.empty
    tc_unwinds  = M.empty
    tc_casts    = M.empty
    tc_hcasts   = M.empty
    tc_defs     = envMap toType $ defs pgm
    tc_fun      = Nothing
    tc_tdefs    = envMap toType $ tDefs pgm
    tc_expr     = Nothing
    tc_verb     = verb


getDefType f 
  = do m <- tc_defs <$> get
       maybe err return $ envFindTy f m 
    where 
       err = tcError l $ errorMissingSpec l f
       l   = srcPos f

-------------------------------------------------------------------------------
getUnwound :: TCM [(Location, Id SourceSpan)]
-------------------------------------------------------------------------------
getUnwound = tc_unwound <$> get

-------------------------------------------------------------------------------
setUnwound :: [(Location, Id SourceSpan)] -> TCM ()
-------------------------------------------------------------------------------
setUnwound ls = modify $ \st -> st { tc_unwound = ls }

-------------------------------------------------------------------------------
addUnwound :: (Location, Id SourceSpan) -> TCM ()
-------------------------------------------------------------------------------
addUnwound l = getUnwound >>= setUnwound . (l:)                                

-----------------------------------------------------------------------------
withUnwound  :: [(Location, Id SourceSpan)] -> TCM a -> TCM a
-----------------------------------------------------------------------------
withUnwound uw action = 
  do  uwold  <- getUnwound 
      setUnwound uw 
      r     <- action 
      setUnwound uw
      return $ r

-----------------------------------------------------------------------------
pushUnwound  :: TCM a -> TCM a
-----------------------------------------------------------------------------
pushUnwound action = 
  do  uwold  <- getUnwound 
      r      <- action 
      setUnwound uwold
      return $ r

-------------------------------------------------------------------------------
setExpr   :: Maybe (Expression AnnSSA) -> TCM () 
-------------------------------------------------------------------------------
setExpr eo = modify $ \st -> st { tc_expr = eo }


-------------------------------------------------------------------------------
getExpr   :: TCM (Maybe (Expression AnnSSA))
-------------------------------------------------------------------------------
getExpr = tc_expr <$> get

--------------------------------------------------------------------------
-- | Generating Fresh Values ---------------------------------------------
--------------------------------------------------------------------------

tick :: TCM Int
tick = do st    <- get 
          let n  = tc_cnt st
          put    $ st { tc_cnt = n + 1 }
          return n 

class Freshable a where 
  fresh :: a -> TCM a 

-- instance Freshable TVar where 
--   fresh _ = TV . F.intSymbol "T" <$> tick

instance Freshable a => Freshable [a] where 
  fresh = mapM fresh

freshTVar l _ =  ((`TV` l). F.intSymbol "T") <$> tick
freshLocation = tick >>= \n -> return ("_?L" ++ show n)

freshHeap :: BHeap -> TCM (Subst,Subst,BHeap)
freshHeap h   = do (θ,θ') <- foldM freshen nilSub (heapLocs h)
                   return (θ, θ', apply θ h)
  where
    nilSub           = (mempty,mempty)
    freshen (θ,θ') l =
          do l' <- freshLocation
             return $ (mappend θ  (Su HM.empty (HM.singleton l l')),
                       mappend θ' (Su HM.empty (HM.singleton l' l)))      

-------------------------------------------------------------------------------
freshHeapVar :: AnnSSA -> String -> TCM (Expression AnnSSA)
-------------------------------------------------------------------------------
freshHeapVar l x
  = do n <- tick
       return $ newVar n idStr
       -- let v = newVar n idStr
       -- modify $ \st -> st { tc_heapExps = M.insertWith (flip (++)) (srcPos l) [v] $ tc_heapExps st }
       -- return v
  where
    newVar n str = VarRef l (Id l (str ++ "_" ++ show n))
    idStr        = printf "%s__%d:%d" x (sourceLine . sp_begin $ srcPos l) (sourceLine . sp_end $ srcPos l)

-- | Monadic unfolding
-------------------------------------------------------------------------------
unfoldFirstTC :: Type -> TCM Type
-------------------------------------------------------------------------------
unfoldFirstTC t = getTDefs >>= \γ -> return $ unfoldFirst γ t


-------------------------------------------------------------------------------
unfoldSafeTC :: Type -> TCM (BHeap, Type)
-------------------------------------------------------------------------------
unfoldSafeTC  t = getTDefs >>= \γ -> return $ unfoldSafe γ t

-------------------------------------------------------------------------------
recordWindExpr :: SourceSpan -> WindCall -> TCM ()
-------------------------------------------------------------------------------
recordWindExpr l p = modify $ \s -> s {
  tc_winds = M.insertWith (flip (++)) l [p] $ tc_winds s
  }

-------------------------------------------------------------------------------
recordUnwindExpr :: SourceSpan -> (Location, Id SourceSpan) -> TCM ()
-------------------------------------------------------------------------------
recordUnwindExpr l p = modify $ \s -> s {
  tc_unwinds = M.insertWith (flip (++)) l [p] $ tc_unwinds s
  }
-------------------------------------------------------------------------------
unwindTC :: Type -> TCM (BHeap, Type)
-------------------------------------------------------------------------------
unwindTC = go heapEmpty
  where go σ t@(TApp (TDef _) _ _) = do
          (σu, tu)  <- unfoldSafeTC t
          (θ,_,σu') <- freshHeap σu
          let σ' = heapCombine [σu',σ]
          case tu of
            t'@(TApp (TDef _) _ _) -> go σ' (apply θ t')
            _                      -> return (σ', apply θ tu)
        go _ _ = error "unwind of a non-TDef"

--------------------------------------------------------------------------------
--  Unification and Subtyping --------------------------------------------------
--------------------------------------------------------------------------------

----------------------------------------------------------------------------------
unifyHeapsM :: (IsLocated l) => l -> String -> BHeap -> BHeap -> TCM Subst
----------------------------------------------------------------------------------
unifyHeapsM l msg σ1 σ2 = do θ <- getSubst
                             γ <- getTDefs
                             case unifyHeaps γ θ σ1 σ2 of
                               Left msg' -> tcError l $ msg ++ "\n" ++ msg'
                               Right θ'  -> do
                                 setSubst θ'
                                 return θ'

----------------------------------------------------------------------------------
unifyTypesM :: (IsLocated l) => l -> String -> [Type] -> [Type] -> TCM Subst
----------------------------------------------------------------------------------
unifyTypesM l msg t1s t2s
  -- TODO: This check might be done multiple times
  | length t1s /= length t2s = tcError l errorArgMismatch 
  | otherwise                = do θ <- getSubst 
                                  γ <- getTDefs
                                  case unifys γ θ t1s t2s of
                                    Left msg' -> tcError l $ msg ++ "\n" ++ msg'
                                    Right θ'  -> do
                                      setSubst θ'
                                      return θ'

----------------------------------------------------------------------------------
safeHeapSubstM :: BHeap -> TCM BHeap
----------------------------------------------------------------------------------
safeHeapSubstM σ = do
  θ <- getSubst
  γ <- getTDefs
  return $ heapFromBinds [(l,t) | (l, Right t) <- heapBinds $ safeHeapSubst γ θ (Right <$> σ)]
                                      
safeHeapSubstWithM f σ = do
  θ <- getSubst
  γ <- getTDefs
  return $ safeHeapSubstWith f γ θ (Right <$> σ)

----------------------------------------------------------------------------------
--unifyTypeM :: (IsLocated l) => l -> String -> Expression AnnSSA -> Type -> Type -> TCM Subst
----------------------------------------------------------------------------------
unifyTypeM l m e t t' = unifyTypesM l msg [t] [t']
  where 
    msg              = errorWrongType m e t t'

----------------------------------------------------------------------------------
subTypeM :: Type -> Type -> TCM SubDirection
----------------------------------------------------------------------------------
subTypeM t t' 
  = do  θ            <- getTDefs 
        let (_,_,_,d) = compareTs θ t t'
        return {- $ tracePP (printf "subTypeM: %s %s %s" (ppshow t) (ppshow d) (ppshow t')) -} d

----------------------------------------------------------------------------------
subTypeM' :: (IsLocated l) => l -> Type -> Type -> TCM ()
----------------------------------------------------------------------------------
subTypeM' _ _ _  = error "unimplemented: subTypeM\'"
 
----------------------------------------------------------------------------------
subTypesM :: [Type] -> [Type] -> TCM [SubDirection]
----------------------------------------------------------------------------------
subTypesM ts ts' = zipWithM subTypeM ts ts'

----------------------------------------------------------------------------------
subHeapM :: Env Type -> BHeap -> BHeap -> TCM SubDirection                   
----------------------------------------------------------------------------------
subHeapM γ σ1 σ2 
  = do let l1s       = sort $ heapLocs σ1
       let l2s       = sort $ heapLocs σ2
       let envLocs   = concat [locs t | (Id _ s, t) <- envToList γ, s /= F.symbolString returnSymbol]
       let ls        = nub $ envLocs ++ l1s
       let σ2'       = restrictHeap ls σ2
       let (com,sup) = partition (`heapMem` σ1) $ heapLocs σ2' 
       let dir       = case filter (`elem` ls) sup of
                          [] -> if l1s == l2s then EqT else SubT
                          _  -> SupT
       ds <- uncurry subTypesM $ mapPair (readTs com) (σ1, σ2')
       return $ foldl (&*&) dir ds

       -- let ls        = nub ((concatMap (locs.snd) $ envToList γ) ++ heapLocs σ)
       -- let (com,sup) = partition (`heapMem` σ) $ heapLocs σ' 
       -- let dir       =  case filter (`elem` ls) sup of
       --                    [] -> if sup == [] then EqT else SubT
       --                    _  -> SupT
       -- ds <- uncurry subTypesM $ mapPair (readTs com) (σ,σ')
       -- return $ foldl (&*&) dir ds
    where readTs ls σ = map (`heapRead` σ) ls

--------------------------------------------------------------------------------
--  cast Helpers ---------------------------------------------------------------
--------------------------------------------------------------------------------


-----------------------------------------------------------------------------
withExpr  :: Maybe (Expression AnnSSA) -> TCM a -> TCM a
-----------------------------------------------------------------------------
withExpr e action = 
  do  eold  <- getExpr 
      setExpr  e 
      r     <- action 
      setExpr  eold
      return $ r


--------------------------------------------------------------------------------
castM     :: Expression AnnSSA -> Type -> Type -> TCM ()
--------------------------------------------------------------------------------
castM e t t'    = subTypeM t t' >>= go
  where go SupT = addDownCast e t'
        go Rel  = addDownCast e t'
        go SubT = addUpCast e t'
        go EqT  = return ()
        go Nth  = addDeadCast e t'

--------------------------------------------------------------------------------
castHeapM :: Env Type -> Expression AnnSSA -> BHeap -> BHeap -> TCM ()
--------------------------------------------------------------------------------
castHeapM γ e σ σ' = subHeapM γ σ σ' >>= go
  where go SupT = addDownCastH e σ'
        go Rel  = addDownCastH e σ'
        go SubT = addUpCastH e σ'
        go EqT  = return ()
        go Nth  = addDeadCastH e σ'


--------------------------------------------------------------------------------
castsM    :: [Expression AnnSSA] -> [Type] -> [Type] -> TCM ()
--------------------------------------------------------------------------------
castsM     = zipWith3M_ castM 


--------------------------------------------------------------------------------
addUpCast :: Expression AnnSSA -> Type -> TCM ()
--------------------------------------------------------------------------------
addUpCast e t = modify $ \st -> st { tc_casts = M.insert e (UCST t) (tc_casts st) }

--------------------------------------------------------------------------------
addDownCast :: Expression AnnSSA -> Type -> TCM ()
--------------------------------------------------------------------------------
addDownCast e t = modify $ \st -> st { tc_casts = M.insert e (DCST t) (tc_casts st) }


--------------------------------------------------------------------------------
addDeadCast :: Expression AnnSSA -> Type -> TCM ()
--------------------------------------------------------------------------------
addDeadCast e t = modify $ \st -> st { tc_casts = M.insert e (DC t) (tc_casts st) } 

--------------------------------------------------------------------------------
addUpCastH :: Expression AnnSSA -> BHeap -> TCM ()
--------------------------------------------------------------------------------
addUpCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (UCST σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
addDownCastH :: Expression AnnSSA -> BHeap -> TCM ()
--------------------------------------------------------------------------------
addDownCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (DCST σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
addDeadCastH:: Expression AnnSSA -> BHeap -> TCM ()
--------------------------------------------------------------------------------
addDeadCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (DC σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
patchPgmM :: (Typeable r, Data r) => Nano AnnSSA (RType r) -> TCM (Nano AnnSSA (RType r))
--------------------------------------------------------------------------------
patchPgmM pgm = 
  do  c    <- tc_casts <$> get
      hc   <- tc_hcasts <$> get
      m    <- tc_winds <$> get
      pgm' <- insertHeapCasts m pgm
      return $ fst $ runState (everywhereM' (mkM transform) pgm') (PS c hc)

data PState = PS { m :: Casts, hm :: HCasts }
type PM     = State PState

insertHeapCasts m pgm = 
  return $ fst $ runState (everywhereM' (mkM go) pgm) (HS m)
  where go :: Statement AnnSSA -> HSM (Statement AnnSSA)
        go s = do
          m <- em <$> get
          let l  = getAnnotation s
          let ws = M.findWithDefault [] (ann l) m
          let es = map (buildWind l) ws 
          put . HS $ M.delete (ann l) m
          return $ if length es == 0 then s else BlockStmt l (map (ExprStmt l) es ++ [s])
        -- 
        windArgs a (l, (Id _ d), et, eh) = [StringLit a l, VarRef a (Id a d), et, eh]
        buildWind a args = CallExpr a (VarRef a (Id a "@Wind")) $ windArgs a args
                                               

data HState = HS { em :: M.Map SourceSpan [WindCall] }
type HSM    = State HState

--------------------------------------------------------------------------------
transform :: Expression AnnSSA -> PM (Expression AnnSSA)
--------------------------------------------------------------------------------
transform e = 
  do  c  <- m <$> get
      hc <- hm <$> get
      put $ PS (M.delete e c) (M.delete e hc)
      return $ patchExpr c hc e

--------------------------------------------------------------------------------
patchExpr :: Casts -> HCasts -> Expression AnnSSA -> Expression AnnSSA
--------------------------------------------------------------------------------
patchExpr m hm e = go a2 AssumeH $ go a1 Assume e
  where a1 = M.lookup e m
        a2 = M.lookup e hm
        a  = getAnnotation e
        fs = ann_fact a
        go (Just (UCST t)) f = UpCast   (a { ann_fact = (f t):fs })
        go (Just (DCST t)) f = DownCast (a { ann_fact = (f t):fs }) 
        go (Just (DC t))   f = DeadCast (a { ann_fact = (f t):fs }) 
        go _               _ = id

-- patchExpr' f m e =
--   case M.lookup e m of
--     Just (UCST t) -> UpCast   (a { ann_fact = (f t):fs }) e
--     Just (DCST t) -> DownCast (a { ann_fact = (f t):fs }) e
--     Just (DC   t) -> DeadCast (a { ann_fact = (f t):fs }) e
--     _             -> e
--   where 
--     fs = ann_fact a
--     a  = getAnnotation e




