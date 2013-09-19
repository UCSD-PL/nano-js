{- LANGUAGE TypeSynonymInstances       #-}
{- LANGUAGE FlexibleInstances          #-}
{- LANGUAGE NoMonomorphismRestriction  #-}
{- LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ImpredicativeTypes        #-}
{-# LANGUAGE LiberalTypeSynonyms       #-}
{-# LANGUAGE FlexibleContexts          #-}

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
  -- , freshTyArgs
  , freshFun
  , freshApp
  , freshLocation
  , freshTVar
  -- , freshSubst
  , freshHeap
  , freshHeapVar
  , tick

  -- * Dot Access
  , safeDotAccess

  -- * Type definitions
  , getTDefs

  -- * Substitutions
  , getSubst, setSubst
  , safeHeapSubstM
  , safeHeapSubstWithM

  -- * Functions
  , getFun, withFun

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
  , addUnwound
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
import           Language.ECMAScript3.PrettyPrint
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
import           Data.Traversable               (traverse)
import           Data.Generics.Aliases
import           Data.Typeable                  (Typeable (..))
import           Language.ECMAScript3.Parser    (SourceSpan (..))
-- import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations

import           Text.Parsec.Pos

import           Debug.Trace                      (trace)
import qualified System.Console.CmdArgs.Verbosity as V

-------------------------------------------------------------------------------
-- | Typechecking monad -------------------------------------------------------
-------------------------------------------------------------------------------

data TCState r = TCS {
                   -- Errors
                     tc_errss    :: ![(SourceSpan, String)]
                   , tc_subst    :: !(RSubst r)
                   , tc_cnt      :: !Int
                   -- Annotations
                   , tc_anns     :: AnnInfo_ r
                   , tc_annss    :: [AnnInfo_ r]
                   -- Heap bookkeeping
                   , tc_unwound  :: [(Location, Id SourceSpan)] 
                   , tc_winds    :: M.Map SourceSpan [WindCall r]
                   , tc_unwinds  :: M.Map SourceSpan [(Location, Id SourceSpan)]
                   -- Cast map: 
                   , tc_casts    :: M.Map (Expression (AnnSSA_ r)) (Cast (RType r))
                   , tc_hcasts   :: M.Map (Expression (AnnSSA_ r)) (Cast (RHeap r))
                   -- Function definitions
                   , tc_defs     :: !(Env (RType r))
                   , tc_fun      :: !(Maybe F.Symbol)
                   -- Type definitions
                   , tc_tdefs    :: !(Env (RType r))
                   -- The currently typed expression 
                   , tc_expr     :: Maybe (Expression (AnnSSA_ r))
                   -- Verbosiry
                   , tc_verb  :: V.Verbosity
                   }

type TCM r    = ErrorT String (State (TCState r))
type WindCall r = (Location, Id SourceSpan, Expression (AnnSSA_ r), Expression (AnnSSA_ r))

-------------------------------------------------------------------------------
whenLoud :: TCM r () -> TCM r ()
-------------------------------------------------------------------------------
whenLoud  act = whenLoud' act $ return ()

-------------------------------------------------------------------------------
whenLoud' :: TCM r a -> TCM r a -> TCM r a
-------------------------------------------------------------------------------
whenLoud' loud other = do  v <- tc_verb <$> get
                           case v of
                             V.Loud -> loud 
                             _      -> other

-------------------------------------------------------------------------------
whenQuiet :: TCM r () -> TCM r ()
-------------------------------------------------------------------------------
whenQuiet  act = whenQuiet' act $ return ()

-------------------------------------------------------------------------------
whenQuiet' :: TCM r a -> TCM r a -> TCM r a
-------------------------------------------------------------------------------
whenQuiet' quiet other = do  v <- tc_verb <$> get
                             case v of
                               V.Quiet -> quiet
                               _       -> other

-------------------------------------------------------------------------------
getTDefs :: TCM r (Env (RType r))
-------------------------------------------------------------------------------
getTDefs = tc_tdefs <$> get 

-------------------------------------------------------------------------------
getSubst :: TCM r (RSubst r)
-------------------------------------------------------------------------------
getSubst = tc_subst <$> get 

getCasts = getCastsF tc_casts

getHCasts = getCastsF tc_hcasts

getCastsF f = do c <- f <$> get
                 return $ M.toList c

-------------------------------------------------------------------------------
setSubst   :: (PP r, F.Reftable r) => RSubst r -> TCM r () 
-------------------------------------------------------------------------------
setSubst θ = modify $ \st -> st { tc_subst = θ }


-------------------------------------------------------------------------------
getFun     :: TCM r (F.Symbol)
-------------------------------------------------------------------------------
getFun   = tc_fun <$> get >>= maybe err return
  where err = error "BUG: no current function!"

-------------------------------------------------------------------------------
withFun     :: F.Symbol -> TCM r a -> TCM r a
-------------------------------------------------------------------------------
withFun f m = do fOld <- tc_fun <$> get
                 modify $ \st -> st { tc_fun = Just f }
                 r <- m
                 modify $ \st -> st { tc_fun = fOld }
                 return r

-------------------------------------------------------------------------------
extSubst :: (F.Reftable r, PP r) => [TVar] -> TCM r ()
-------------------------------------------------------------------------------
extSubst βs = getSubst >>= setSubst . (`mappend` θ')
  where 
    θ'      = fromLists (zip βs (tVar <$> βs)) []


-------------------------------------------------------------------------------
tcError :: (IsLocated l) => l -> String -> TCM r a
-------------------------------------------------------------------------------
tcError l msg = throwError $ printf "TC-ERROR at %s : %s" (ppshow $ srcPos l) msg


-------------------------------------------------------------------------------
logError   :: SourceSpan -> String -> a -> TCM r a
-------------------------------------------------------------------------------
logError l msg x = (modify $ \st -> st { tc_errss = (l,msg):(tc_errss st)}) >> return x


-------------------------------------------------------------------------------
freshFun :: (PP r, PP fn, F.Reftable r) =>
  AnnSSA_ r -> fn -> RType r -> TCM r ([TVar], [Bind r], RHeap r, RHeap r, RType r)
-------------------------------------------------------------------------------
freshFun l fn ft
  = do let bkft           =  bkAll ft
       t'                <- freshTyArgs (srcPos l) (bkAll ft)
       (ts,ibs,σi,σo :: RHeap r,ot) <- maybe err return $ bkFun t'
       let ls             = nub $ heapLocs σi ++ heapLocs σo
       ls'               <- mapM (const freshLocation') ls
       let θl             = fromLists [] (zip ls ls') :: RSubst r
       let (σi',σo')      = mapPair (apply θl) (σi, σo)
       let ibs'           = apply θl <$> ibs
       let ot'            = apply θl ot
       addAnn (srcPos l) $ FunInst (zip (fst bkft) (tVar <$> ts)) (zip ls ls')
       return (ts, ibs', σi', σo', ot')
  where
    err = logError (ann l) (errorNonFunction fn ft) tFunErr
    
freshApp l i@(Id _ d)
  = do γ <- getTDefs
       case envFindTy d γ of
         Just (TBd (TD _ vs _ _ _)) -> freshen i vs
         _                          -> err γ
    where
      err     γ    = logError (ann l) (errorUnboundIdEnv d γ) tErr
      mkApp   i vs = TApp (TDef i) vs F.top
      freshen i vs = do vs' <- mapM (freshTVar (ann l)) vs
                        extSubst vs'
                        return $ mkApp i $ tVar <$> vs'
      

-------------------------------------------------------------------------------
freshLocation :: AnnSSA_ r -> TCM r Location
-------------------------------------------------------------------------------
freshLocation l = do loc <- freshLocation' 
                     addAnn (srcPos l) $ LocInst loc
                     return loc
       
-------------------------------------------------------------------------------
freshTyArgs :: (PP r, F.Reftable r) => SourceSpan -> ([TVar], RType r) -> TCM r (RType r)
-------------------------------------------------------------------------------
freshTyArgs l (αs, t) 
  = (`apply` t) <$> freshSubst l αs

freshSubst :: (PP r, F.Reftable r) => SourceSpan -> [TVar] -> TCM r (RSubst r)
freshSubst l αs
  = do
      fUnique αs
      βs        <- mapM (freshTVar l) αs
      -- setTyArgs l βs
      extSubst βs 
      return     $ fromLists (zip αs (tVar <$> βs)) []
    where
      fUnique xs = when (not $ unique xs) $ logError l errorUniqueTypeParams ()

-- setTyArgs l βs 
--   = do m <- tc_anns <$> get 
--        when (HM.member l m) $ tcError l "Multiple Type Args"
--        addAnn l $ TypInst (tVar <$> βs)


-------------------------------------------------------------------------------
-- | Field access -------------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
safeDotAccess :: (Ord r, PP r, F.Reftable r, 
                  Substitutable r (Fact_ r), Free (Fact_ r), 
                  F.Symbolic s, PP s) =>
  RHeap r -> s -> RType r -> TCM r [(Location, ObjectAccess r)]
-------------------------------------------------------------------------------
safeDotAccess σ f t@(TApp TUn ts _)  = 
  do as         <- mapM (safeDotAccess σ f) ts
     let tsas    = [ (t, l, a) | (t, (l,a)) <- zip ts (concat as) ]
     let (ts',ls,as) = unzip3 tsas
     e          <- fromJust <$> getExpr
     e'         <- freshHeapVar (getAnnotation e) (printf "ptr(%s)__" (ppshow e))
     castM e' t (mkUnion ts')
     return $ zip ls as

safeDotAccess σ f t 
  = do ma <- safeDotAccess' σ f t
       case ma of
         Nothing     -> return []
         Just (l,a)  -> case ac_unfold a of
                          Just (i, _) -> addUnwound (l, i) >> return [(l, a)]
                          _           -> return  [(l, a)] 
-------------------------------------------------------------------------------
safeDotAccess' :: (Ord r, PP r, F.Reftable r, 
                  Substitutable r (Fact_ r), Free (Fact_ r), 
                  F.Symbolic s, PP s) =>
  RHeap r -> s -> RType r -> TCM r (Maybe (Location, ObjectAccess r))
-------------------------------------------------------------------------------
safeDotAccess' σ f t@(TApp (TRef l) _ _)
  = do γ       <- getTDefs
       e       <- fromJust <$> getExpr
       e'      <- freshHeapVar (getAnnotation e) (printf "%s__" (ppshow e))
       -- Get a list of all the possible types at locatioin "l"
       -- including unfolded types and heaps, then freshen each
       -- and join
       case dotAccessRef (γ,σ) f t of
         Nothing -> return Nothing -- error "safeDotAccess: unsafe"
         Just as -> do a <- joinAccess <$> traverse freshen as
                       castM e' (heapRead l σ) (ac_cast a)
                       return $ Just (l, a) 
  where
    safeUnfoldTy [(i,t)] = (i,t)
    safeUnfoldTy _       = error $ "TBD: handle fancy unions"
    joinAccess as = Access { ac_result = mkUnion $ ac_result <$> as
                           , ac_cast   = mkUnion $ ac_cast   <$> as
                           , ac_unfold = safeUnfoldTy <$> traverse ac_unfold as
                           , ac_heap   = heapCombine  <$> traverse ac_heap as
                           }
    freshen a = case ac_heap a of
                  Nothing -> return a
                  Just σ  -> do (θ,_,σ') <- freshHeap σ
                                return $ a { ac_result = apply θ  $  ac_result a
                                           , ac_cast   = apply θ  $ ac_cast a
                                           , ac_heap   = Just σ'
                                           , ac_unfold = fmap (apply θ) <$> ac_unfold a
                                           }

safeDotAccess' σ f _ = return Nothing
    
-------------------------------------------------------------------------------
-- | Managing Annotations: Type Instantiations --------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
getAnns :: (Ord r, F.Reftable r, Substitutable r (Fact_ r)) => TCM r (AnnInfo_ r)
-------------------------------------------------------------------------------
getAnns = do θ     <- tc_subst <$> get
             m     <- tc_anns  <$> get
             let m' = fmap (apply θ . sortNub) m
             _     <- modify $ \st -> st { tc_anns = m' }
             return m' 

-------------------------------------------------------------------------------
addAnn :: SourceSpan -> Fact_ r -> TCM r () 
-------------------------------------------------------------------------------
addAnn l f = modify $ \st -> st { tc_anns = inserts l f (tc_anns st) } 

-------------------------------------------------------------------------------
getAllAnns :: TCM r [AnnInfo_ r]  
-------------------------------------------------------------------------------
getAllAnns = tc_annss <$> get


-------------------------------------------------------------------------------
accumAnn :: (Ord r, F.Reftable r, Substitutable r (Fact_ r)) =>
  (AnnInfo_ r -> [(SourceSpan, String)]) -> TCM r () -> TCM r ()
-------------------------------------------------------------------------------
accumAnn check act 
  = do m     <- tc_anns <$> get 
       modify $ \st -> st {tc_anns = HM.empty}
       act
       m'    <- getAnns
       forM_ (check m') $ \(l, s) -> logError l s ()
       modify $ \st -> st {tc_anns = m} {tc_annss = m' : tc_annss st}

-------------------------------------------------------------------------------
execute     ::  (PP r, F.Reftable r) => V.Verbosity -> Nano z (RType r) -> TCM r a -> Either [(SourceSpan, String)] a
-------------------------------------------------------------------------------
execute verb pgm act 
  = case runState (runErrorT act) $ initState verb pgm of 
      (Left err, _) -> Left [(dummySpan,  err)]
      (Right x, st) ->  applyNonNull (Right x) Left (reverse $ tc_errss st)


initState :: (PP r, F.Reftable r) => V.Verbosity -> Nano z (RType r) -> TCState r
initState verb pgm = TCS { tc_errss   = []
                         , tc_subst   = mempty
                         , tc_cnt     = 0
                         , tc_anns    = HM.empty
                         , tc_annss   = []
                         , tc_unwound = []
                         , tc_winds   = M.empty
                         , tc_unwinds = M.empty
                         , tc_casts   = M.empty
                         , tc_hcasts  = M.empty
                         , tc_defs    = defs pgm
                         , tc_fun     = Nothing
                         , tc_tdefs   = tDefs pgm
                         , tc_expr    = Nothing
                         , tc_verb    = verb
                         }

getDefType f 
  = do m <- tc_defs <$> get
       maybe err return $ envFindTy f m 
    where 
       err = tcError l $ errorMissingSpec l f
       l   = srcPos f

-------------------------------------------------------------------------------
getUnwound :: TCM r [(Location, Id SourceSpan)]
-------------------------------------------------------------------------------
getUnwound = tc_unwound <$> get

-------------------------------------------------------------------------------
setUnwound :: [(Location, Id SourceSpan)] -> TCM r ()
-------------------------------------------------------------------------------
setUnwound ls = modify $ \st -> st { tc_unwound = ls }

-------------------------------------------------------------------------------
addUnwound :: (Location, Id SourceSpan) -> TCM r ()
-------------------------------------------------------------------------------
addUnwound l = getUnwound >>= setUnwound . (l:)                                

-----------------------------------------------------------------------------
withUnwound  :: [(Location, Id SourceSpan)] -> TCM r a -> TCM r a
-----------------------------------------------------------------------------
withUnwound uw action = 
  do  uwold  <- getUnwound 
      setUnwound uw 
      r     <- action 
      setUnwound uw
      return $ r

-----------------------------------------------------------------------------
pushUnwound  :: TCM r a -> TCM r a
-----------------------------------------------------------------------------
pushUnwound action = 
  do  uwold  <- getUnwound 
      r      <- action 
      setUnwound uwold
      return $ r

-------------------------------------------------------------------------------
setExpr   :: Maybe (Expression (AnnSSA_ r)) -> TCM r () 
-------------------------------------------------------------------------------
setExpr eo = modify $ \st -> st { tc_expr = eo }


-------------------------------------------------------------------------------
getExpr   :: TCM r (Maybe (Expression (AnnSSA_ r)))
-------------------------------------------------------------------------------
getExpr = tc_expr <$> get

--------------------------------------------------------------------------
-- | Generating Fresh Values ---------------------------------------------
--------------------------------------------------------------------------

tick :: TCM r Int
tick = do st    <- get 
          let n  = tc_cnt st
          put    $ st { tc_cnt = n + 1 }
          return n 

class Freshable a where 
  fresh :: a -> TCM r a

-- instance Freshable TVar where 
--   fresh _ = TV . F.intSymbol "T" <$> tick

instance Freshable a => Freshable [a] where 
  fresh = mapM fresh

freshTVar :: SourceSpan -> a -> TCM r (TVar)
freshTVar l _ =  ((`TV` l). F.intSymbol "T") <$> tick

-------------------------------------------------------------------------------
freshHeap :: (PP r, Ord r, F.Reftable r) => 
  RHeap r -> TCM r (RSubst r,RSubst r,RHeap r)
-------------------------------------------------------------------------------
freshHeap h   = do (θ,θ') <- foldM freshen nilSub (heapLocs h)
                   return (θ, θ', apply θ h)
  where
    nilSub           = (mempty,mempty)
    freshen (θ,θ') l =
          do l' <- freshLocation'
             return $ (mappend θ  (Su HM.empty (HM.singleton l l')),
                       mappend θ' (Su HM.empty (HM.singleton l' l)))      

freshLocation' = tick >>= \n -> return ("_?L" ++ show n)

-------------------------------------------------------------------------------
freshHeapVar :: AnnSSA_ r -> String -> TCM r (Expression (AnnSSA_ r))
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
unfoldFirstTC :: (PP r, F.Reftable r) => RType r -> TCM r (RType r)
-------------------------------------------------------------------------------
unfoldFirstTC t = getTDefs >>= \γ -> return $ unfoldFirst γ t


-------------------------------------------------------------------------------
unfoldSafeTC :: (PP r, F.Reftable r) => RType r -> TCM r (RHeap r, RType r)
-------------------------------------------------------------------------------
unfoldSafeTC  t = getTDefs >>= \γ -> return $ unfoldSafe γ t

-------------------------------------------------------------------------------
recordWindExpr :: SourceSpan -> WindCall r -> TCM r ()
-------------------------------------------------------------------------------
recordWindExpr l p = modify $ \s -> s {
  tc_winds = M.insertWith (flip (++)) l [p] $ tc_winds s
  }

-------------------------------------------------------------------------------
recordUnwindExpr :: SourceSpan -> (Location, Id SourceSpan) -> TCM r ()
-------------------------------------------------------------------------------
recordUnwindExpr l p = modify $ \s -> s {
  tc_unwinds = M.insertWith (flip (++)) l [p] $ tc_unwinds s
  }

-------------------------------------------------------------------------------
unwindTC :: (PP r, Ord r, F.Reftable r) =>
  RType r -> TCM r (RHeap r, RType r)
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
unifyHeapsM :: (IsLocated l, Ord r, PP r, F.Reftable r) =>
  l -> String -> RHeap r -> RHeap r -> TCM r (RSubst r)
----------------------------------------------------------------------------------
unifyHeapsM l msg σ1 σ2 = do θ <- getSubst
                             γ <- getTDefs
                             case unifyHeaps γ θ σ1 σ2 of
                               Left msg' -> tcError l $ msg ++ "\n" ++ msg'
                               Right θ'  -> do
                                 setSubst θ'
                                 return θ'

----------------------------------------------------------------------------------
unifyTypesM :: (IsLocated l, Ord r, PP r, F.Reftable r) => l -> String -> [RType r] -> [RType r] -> TCM r (RSubst r)
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
safeHeapSubstM :: (Ord r, PP r, F.Reftable r) =>
  RHeap r -> TCM r (RHeap r)
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
unifyTypeM :: (Ord r, PrintfArg t1, PP r, PP a, F.Reftable r, IsLocated l) =>
  l -> t1 -> a -> RType r -> RType r -> TCM r (RSubst r)
----------------------------------------------------------------------------------
unifyTypeM l m e t t' = unifyTypesM l msg [t] [t']
  where 
    msg              = errorWrongType m e t t'

----------------------------------------------------------------------------------
subTypeM :: (Ord r, PP r, F.Reftable r) => RType r -> RType r -> TCM r SubDirection
----------------------------------------------------------------------------------
subTypeM t t' 
  = do  θ            <- getTDefs 
        let (_,_,_,d) = compareTs θ t t'
        return {- $ tracePP (printf "subType: %s %s %s" (ppshow t) (ppshow d) (ppshow t')) -} d

----------------------------------------------------------------------------------
subTypeM' :: (IsLocated l, Ord r, PP r, F.Reftable r) => l -> RType r -> RType r -> TCM r ()
----------------------------------------------------------------------------------
subTypeM' _ _ _  = error "unimplemented: subTypeM\'"
 
----------------------------------------------------------------------------------
subTypesM :: (Ord r, PP r, F.Reftable r) => [RType r] -> [RType r] -> TCM r [SubDirection]
----------------------------------------------------------------------------------
subTypesM ts ts' = zipWithM subTypeM ts ts'

----------------------------------------------------------------------------------
subHeapM :: (Ord r, PP r, F.Reftable r) =>
  Env (RType r) -> RHeap r -> RHeap r -> TCM r SubDirection                   
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
withExpr  :: Maybe (Expression (AnnSSA_ r)) -> TCM r a -> TCM r a
-----------------------------------------------------------------------------
withExpr e action = 
  do  eold  <- getExpr 
      setExpr  e 
      r     <- action 
      setExpr  eold
      return $ r


--------------------------------------------------------------------------------
castM     :: (Ord r, PP r, F.Reftable r) => Expression (AnnSSA_ r) -> RType r -> RType r -> TCM r ()
--------------------------------------------------------------------------------
castM e t t'    = subTypeM t t' >>= go
  where go SupT = addDownCast e t t'
        go Rel  = addDownCast e t t'
        go SubT = addUpCast e t'
        go EqT  = return ()
        go Nth  = addDeadCast e t'

--------------------------------------------------------------------------------
castHeapM :: (Ord r, PP r, F.Reftable r) =>
  Env (RType r) -> Expression (AnnSSA_ r) -> RHeap r -> RHeap r -> TCM r ()
--------------------------------------------------------------------------------
castHeapM γ e σ σ' = subHeapM γ σ σ' >>= go
  where go SupT = addDownCastH e σ'
        go Rel  = addDownCastH e σ'
        go SubT = addUpCastH e σ'
        go EqT  = return ()
        go Nth  = addDeadCastH e σ'


--------------------------------------------------------------------------------
castsM    :: (Ord r, PP r, F.Reftable r) => [Expression (AnnSSA_ r)] -> [RType r] -> [RType r] -> TCM r ()
--------------------------------------------------------------------------------
castsM     = zipWith3M_ castM 


--------------------------------------------------------------------------------
addUpCast :: (F.Reftable r, PP r) => Expression (AnnSSA_ r) -> RType r -> TCM r ()
--------------------------------------------------------------------------------
addUpCast e t = modify $ \st -> st { tc_casts = M.insert e (UCST t) (tc_casts st) }

--------------------------------------------------------------------------------
addDownCast :: (Ord r, PP r, F.Reftable r) => Expression (AnnSSA_ r) -> RType r -> RType r -> TCM r ()
--------------------------------------------------------------------------------
-- addDownCast e _ cast = modify $ \st -> st { tc_casts = M.insert e (DCST cast) (tc_casts st) }

  
-- Down casts will not be k-vared later - so pass the refinements here!
addDownCast e base cast = 
  do  γ <- getTDefs
      let cast' = zipType2 γ F.meet base cast    -- copy the refinements from the base type 
          {-msg   =  printf "DOWN CAST ADDS: %s\ninstead of just:\n%s" (ppshow cast') (ppshow cast)-}
      modify $ \st -> st { tc_casts = M.insert e (DCST $ {- trace msg -} cast') (tc_casts st) }

--------------------------------------------------------------------------------
addDeadCast :: Expression (AnnSSA_ r) -> RType r -> TCM r ()
--------------------------------------------------------------------------------
addDeadCast e t = modify $ \st -> st { tc_casts = M.insert e (DC t) (tc_casts st) }

--------------------------------------------------------------------------------
addUpCastH :: Expression (AnnSSA_ r) -> RHeap r -> TCM r ()
--------------------------------------------------------------------------------
addUpCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (UCST σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
addDownCastH :: Expression (AnnSSA_ r) -> RHeap r -> TCM r ()
--------------------------------------------------------------------------------
addDownCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (DCST σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
addDeadCastH:: Expression (AnnSSA_ r) -> RHeap r -> TCM r ()
--------------------------------------------------------------------------------
addDeadCastH e σ = modify $ \st -> st { tc_hcasts = M.insert e (DC σ) (tc_hcasts st) }

--------------------------------------------------------------------------------
patchPgmM :: (Data b, Typeable r) => b -> TCM r b
--------------------------------------------------------------------------------
patchPgmM pgm = 
  do  c    <- tc_casts <$> get
      hc   <- tc_hcasts <$> get
      m    <- tc_winds <$> get
      pgm' <- insertHeapCasts m pgm
      return $ fst $ runState (everywhereM' (mkM transform) pgm') (PS c hc)

data PState r = PS { m :: Casts_ r, hm :: HCasts_ r}
type PM     r = State (PState r)

insertHeapCasts m pgm = 
  return $ fst $ runState (everywhereM' (mkM go) pgm) (HS m)
  where go :: Statement (AnnSSA_ r) -> HSM r (Statement (AnnSSA_ r))
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
                                               

data HState r = HS { em :: M.Map SourceSpan [WindCall r] }
type HSM    r = State (HState r)

--------------------------------------------------------------------------------
transform :: Expression (AnnSSA_ r) -> PM r (Expression (AnnSSA_ r))
--------------------------------------------------------------------------------
transform e = 
  do  c  <- m <$> get
      hc <- hm <$> get
      put $ PS (M.delete e c) (M.delete e hc)
      return $ patchExpr c hc e

--------------------------------------------------------------------------------
patchExpr :: Casts_ r -> HCasts_ r -> Expression (AnnSSA_ r) -> Expression (AnnSSA_ r)
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




