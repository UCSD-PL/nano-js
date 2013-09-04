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

  -- * Dot Access
  , dotAccess

  -- * Type definitions
  , getTDefs

  -- * Substitutions
  , getSubst, setSubst

  -- * Functions
  , getFun, setFun

  -- * Annotations
  , accumAnn
  , getAllAnns

  -- * Unfolding
  , unfoldFirstTC, unfoldSafeTC, unwindTC

  -- * Subtyping
  , subTypeM  , subTypeM'
  , subTypesM , subHeapM

  -- * Unification
  , unifyTypeM, unifyTypesM

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
import           Language.Nano.Misc             (unique, everywhereM', zipWith3M_, fst4)
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
import           Data.List                      (find, partition, nub)
import           Data.Generics.Aliases
import           Data.Typeable                  (Typeable (..))
import           Language.ECMAScript3.Parser    (SourceSpan (..))
-- import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations

-- import           Debug.Trace                      (trace)
import qualified System.Console.CmdArgs.Verbosity as V

-------------------------------------------------------------------------------
-- | Typechecking monad -------------------------------------------------------
-------------------------------------------------------------------------------

data TCState = TCS { 
                   -- Errors
                     tc_errss :: ![(SourceSpan, String)]
                   , tc_subst :: !Subst
                   , tc_cnt   :: !Int
                   -- Annotations
                   , tc_anns  :: AnnInfo
                   , tc_annss :: [AnnInfo]
                   -- Cast map: 
                   , tc_casts  :: M.Map (Expression AnnSSA) (Cast Type)
                   , tc_hcasts :: M.Map (Expression AnnSSA) (Cast (Heap Type))
                   -- Function definitions
                   , tc_defs  :: !(Env Type) 
                   , tc_fun   :: !(Maybe F.Symbol)
                   -- Type definitions
                   , tc_tdefs :: !(Env Type)
                   -- The currently typed expression 
                   , tc_expr  :: Maybe (Expression AnnSSA)

                   -- Verbosiry
                   , tc_verb  :: V.Verbosity
                   }

type TCM     = ErrorT String (State TCState)


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
       when (HM.member l m) $ tcError l "Multiple Type Args"
       addAnn l $ TypInst (tVar <$> βs)


-------------------------------------------------------------------------------
-- | Field access -------------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
dotAccess :: Id AnnSSA -> Type -> TCM (Maybe Type)
-------------------------------------------------------------------------------
dotAccess f   (TObj bs _) = 
  return $ Just $ maybe tUndef b_type $ find (match $ F.symbol f) bs
  where match s (B f _)  = s == f

dotAccess f t@(TApp c ts _ ) = go c
  where  go TUn      = dotAccessUnion f ts
         go TInt     = return $ Just tUndef
         go TBool    = return $ Just tUndef
         go TString  = return $ Just tUndef
         go TUndef   = return   Nothing
         go TNull    = return   Nothing
         go (TDef _) = unfoldSafeTC t >>= (dotAccess f . snd)
         go TTop     = error "dotAccess top"
         go TVoid    = error "dotAccess void"
         go (TRef _)  = error "dotAccess ref"

dotAccess _   (TFun _ _ _ _ _ ) = return $ Just tUndef
dotAccess _ t               = error $ "dotAccess " ++ (ppshow t) 


-------------------------------------------------------------------------------
dotAccessUnion :: Id AnnSSA -> [Type] -> TCM (Maybe Type)
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
        _  -> return $ Just $ mkUnion tfs'

      

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
initState verb pgm = TCS tc_errss tc_subst tc_cnt tc_anns tc_annss 
                       tc_casts tc_hcasts tc_defs tc_fun tc_tdefs tc_expr tc_verb 
  where
    tc_errss  = []
    tc_subst  = mempty 
    tc_cnt    = 0
    tc_anns   = HM.empty
    tc_annss  = []
    tc_casts  = M.empty
    tc_hcasts = M.empty
    tc_defs   = envMap toType $ defs pgm
    tc_fun    = Nothing
    tc_tdefs  = envMap toType $ tDefs pgm
    tc_expr   = Nothing
    tc_verb   = verb


getDefType f 
  = do m <- tc_defs <$> get
       maybe err return $ envFindTy f m 
    where 
       err = tcError l $ errorMissingSpec l f
       l   = srcPos f


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

--------------------------------------------------------------------------------
--  Unification and Subtyping --------------------------------------------------
--------------------------------------------------------------------------------


----------------------------------------------------------------------------------
unifyTypesM :: (IsLocated l) => l -> String -> BHeap -> [Type] -> [Type] -> TCM (Subst, BHeap)
----------------------------------------------------------------------------------
unifyTypesM l msg σ t1s t2s
  -- TODO: This check might be done multiple times
  | length t1s /= length t2s = tcError l errorArgMismatch 
  | otherwise                = do θ <- getSubst 
                                  γ <- getTDefs
                                  case unifys (γ,σ) θ t1s t2s of
                                    Left msg'     -> tcError l $ msg ++ "\n" ++ msg'
                                    Right (θ',σ') -> setSubst θ' >> return (θ', unifyHeapM γ θ' σ')

-- Unification may have resulted in heap locations that need to be merged
unifyHeapM γ θ σ = foldl joinLoc heapEmpty . map (apply θ) . heapBinds $ σ
    where safeAdd t1 t2   = fst4 $ compareTs γ t1 t2
          joinLoc σ (l,t) = heapAddWith safeAdd l t σ
----------------------------------------------------------------------------------
--unifyTypeM :: (IsLocated l) => l -> String -> Expression AnnSSA -> Type -> Type -> TCM Subst
----------------------------------------------------------------------------------
unifyTypeM l m σ e t t' = unifyTypesM l msg σ [t] [t']
  where 
    msg              = errorWrongType m e t t'

----------------------------------------------------------------------------------
subTypeM :: Type -> Type -> TCM SubDirection
----------------------------------------------------------------------------------
subTypeM t t' 
  = do  θ            <- getTDefs 
        let (_,_,_,d) = compareTs θ t t'
        return $ {- tracePP (printf "subTypeM: %s %s %s" (ppshow t) (ppshow d) (ppshow t')) -} d

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
subHeapM γ σ σ' 
  = do let ls = nub ((concatMap (locs.snd) $ envToList γ)
                       ++ heapLocs σ)
       let (com,sup) = partition (`heapMem` σ) $ heapLocs σ' 
       let dir       =  case filter (`elem` ls) sup of
                          [] -> SubT
                          _  -> SupT
       ds <- uncurry subTypesM $ mapPair (readTs com) (σ,σ')
       return $ foldl (&*&) dir ds
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
  do  c  <- tc_casts <$> get
      hc <- tc_hcasts <$> get
      return $ fst $ runState (everywhereM' (mkM transform) pgm) (PS c hc)


data PState = PS { m :: Casts, hm :: HCasts }
type PM     = State PState

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




