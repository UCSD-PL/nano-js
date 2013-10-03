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
  , recordingUnwind
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
    -- * Statement Getter/Setter
  , getStmt, setStmt

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
import           Language.Nano.Typecheck.WindFuns
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Unify
import           Language.Nano.Errors
import           Data.Function                  (on)                  
import           Data.Monoid                  
import qualified Data.HashMap.Strict            as HM
import qualified Data.Map                       as M
import           Data.Generics                  (Data(..))
import           Data.Maybe                     (fromJust)
import           Data.List                      (find, partition, nub, sort, unzip4, intersect, deleteFirstsBy)
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
                   , tc_unwound  :: [(Location, Id SourceSpan, RSubst r)] 
                   , tc_winds    :: M.Map SourceSpan [WindCall r]
                   , tc_unwinds  :: M.Map SourceSpan [(Location, Id SourceSpan)]
                   , tc_heapexps :: M.Map SourceSpan [Expression (AnnSSA_ r)]
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
                   -- The currently typed expression 
                   , tc_stmt     :: Maybe (Statement (AnnSSA_ r))
                   -- Verbosiry
                   , tc_verb  :: V.Verbosity
                   }

type TCM r    = ErrorT String (State (TCState r))
type WindCall r = (Location, Id SourceSpan)

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
  = do let bkft           = bkAll ft
       (τs,t')          <- freshTyArgs (srcPos l) bkft
       (ts,ibs,σi,σo :: RHeap r,ot) <- maybe err return $ bkFun t'
       let ls             = nub $ heapLocs σi ++ heapLocs σo
       ls'               <- mapM (const freshLocation') ls
       let θl             = fromLists [] (zip ls ls') :: RSubst r
       let (σi',σo')      = mapPair (apply θl) (σi, σo)
       let ibs'           = apply θl <$> ibs
       let ot'            = apply θl ot
       addAnn (srcPos l) $ FunInst (zip (fst bkft) τs) (zip ls ls')
       return (ts, ibs', σi', σo', ot')
  where
    err = logError (ann l) (errorNonFunction fn ft) tFunErr
    
freshApp :: (F.Reftable r, PP r) => AnnSSA_ r -> Id SourceSpan -> TCM r (RSubst r, RType r) 
freshApp l i@(Id _ d)
  = do γ <- getTDefs
       case envFindTy d γ of
         Just (TBd (TD _ vs _ _ _)) -> freshen i vs
         _                          -> err γ
    where
      err     γ    = logError (ann l) (errorUnboundIdEnv d γ) (mempty, tErr)
      mkApp   i vs = TApp (TDef i) vs F.top
      freshen i vs = do vs' <- mapM (freshTVar (ann l)) vs
                        extSubst vs'
                        let tVs = tVar <$> vs'
                        return (fromLists (zip vs tVs) [], mkApp i tVs)
      

-------------------------------------------------------------------------------
freshLocation :: AnnSSA_ r -> TCM r Location
-------------------------------------------------------------------------------
freshLocation l = do loc <- freshLocation' 
                     addAnn (srcPos l) $ LocInst loc
                     return loc
       
-------------------------------------------------------------------------------
freshTyArgs :: (PP r, F.Reftable r) => SourceSpan -> ([TVar], RType r) -> TCM r ([RType r],RType r)
-------------------------------------------------------------------------------
freshTyArgs l (αs, t) 
  = (`apply` (tVar <$> αs,t)) <$> freshSubst l αs

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
  do as         <- mapM (safeDotAccess σ f . tRef) $ nub $ concatMap locs ts
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
                          Just (i, θ, _) -> addu (l,i,θ,a)-- addUnwound (l, i, θ) >> return [(l, a)]
                          _              -> return  [(l, a)] 
    where addu (l,i,θ,a) = do m <- maybe err getAnn =<< getStmt 
                              recordUnwindExpr m (l,i,θ)
                              return [(l,a)]
          err            = error "BUG: no statement safeDotAccess"
          getAnn         = return . ann . getAnnotation
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
       -- Get a list of all the possible types at location "l"
       -- including unfolded types and heaps, then freshen each
       -- and join
       case dotAccessRef (γ,σ) f t of
         Nothing -> return Nothing -- error "safeDotAccess: unsafe"
         Just as -> do a <- joinAccess <$> traverse freshen as
                       castM e' (heapRead "safeDotAccess'" l σ) (ac_cast a)
                       return $ Just (l, a) 
  where
    safeUnfoldTy [u] = u
    safeUnfoldTy _       = error $ "TBD: handle fancy unions"
    joinAccess as = Access { ac_result = mkUnion $ ac_result <$> as
                           , ac_cast   = mkUnion $ ac_cast   <$> as
                           , ac_unfold = safeUnfoldTy <$> traverse ac_unfold as
                           , ac_heap   = heapCombine  <$> traverse ac_heap as
                           }
    freshen a = case ac_heap a of
                  Nothing -> return a
                  Just σ  -> do (θ,_,σ') <- freshHeap σ
                                return $ a { ac_result = apply θ  $ ac_result a
                                           , ac_cast   = apply θ  $ ac_cast a
                                           , ac_heap   = Just σ'
                                           , ac_unfold = appUf θ <$> ac_unfold a
                                           }
    appUf θ (l,θ',t) = (l, θ' `mappend` θ, apply θ t)

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
                         , tc_heapexps= M.empty
                         , tc_hcasts  = M.empty
                         , tc_defs    = defs pgm
                         , tc_fun     = Nothing
                         , tc_tdefs   = tDefs pgm
                         , tc_expr    = Nothing
                         , tc_stmt    = Nothing
                         , tc_verb    = verb
                         }

getDefType f 
  = do m <- tc_defs <$> get
       maybe err return $ envFindTy f m 
    where 
       err = tcError l $ errorMissingSpec l f
       l   = srcPos f

-------------------------------------------------------------------------------
getUnwound :: TCM r [(Location, Id SourceSpan, RSubst r)]
-------------------------------------------------------------------------------
getUnwound = tc_unwound <$> get

-------------------------------------------------------------------------------
setUnwound :: [(Location, Id SourceSpan, RSubst r)] -> TCM r ()
-------------------------------------------------------------------------------
setUnwound ls = modify $ \st -> st { tc_unwound = ls }

-------------------------------------------------------------------------------
addUnwound :: (Location, Id SourceSpan, RSubst r) -> TCM r ()
-------------------------------------------------------------------------------
addUnwound l = getUnwound >>= setUnwound . (l:)                                

-----------------------------------------------------------------------------
withUnwound  :: [(Location, Id SourceSpan, RSubst r)] -> TCM r a -> TCM r a
-----------------------------------------------------------------------------
withUnwound uw action = 
  do  uwold  <- getUnwound 
      setUnwound uw 
      r     <- action 
      setUnwound uwold
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

-------------------------------------------------------------------------------
setStmt   :: Maybe (Statement (AnnSSA_ r)) -> TCM r () 
-------------------------------------------------------------------------------
setStmt so = modify $ \st -> st { tc_stmt = so }

-------------------------------------------------------------------------------
getStmt   :: TCM r (Maybe (Statement (AnnSSA_ r)))
-------------------------------------------------------------------------------
getStmt = tc_stmt <$> get

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
       -- return $ newVar n idStr
       let v = newVar n idStr
       -- modify $ \st -> st { tc_heapexps = M.insertWith (flip (++)) (srcPos l) [v] $ tc_heapexps st }
       return v
  where
    newVar n str = VarRef l (Id l (str ++ "_" ++ show n))
    idStr        = printf "%s__%d:%d" x (sourceLine . sp_begin $ srcPos l) (sourceLine . sp_end $ srcPos l)

-- | Monadic unfolding
-------------------------------------------------------------------------------
unfoldFirstTC :: (PP r, F.Reftable r) => RType r -> TCM r (RType r)
-------------------------------------------------------------------------------
unfoldFirstTC t = getTDefs >>= \γ -> return $ unfoldFirst γ t


-------------------------------------------------------------------------------
unfoldSafeTC :: (PP r, F.Reftable r) => RType r -> TCM r (RHeap r, RType r, RSubst r)
-------------------------------------------------------------------------------
unfoldSafeTC  t = getTDefs >>= \γ -> return $ unfoldSafe γ t

-------------------------------------------------------------------------------
recordWindExpr :: (PP r, F.Reftable r) => 
  SourceSpan -> WindCall r -> RSubst r -> TCM r ()
-------------------------------------------------------------------------------
recordWindExpr l p@(loc,t) θ 
  = addWind >> addAnn (srcPos l) windInst
  where
    windInst = uncurry (WindInst loc t) $ toLists θ
    addWind  = modify $ \s -> s {
      tc_winds = M.insertWith (flip (++)) l [tracePP "RECORDING WIND" p `seq`p] $ tc_winds s
      }

-------------------------------------------------------------------------------
recordingUnwind :: (PP r, Ord r, F.Reftable r) => 
  SourceSpan -> TCM r a -> TCM r a
-------------------------------------------------------------------------------
recordingUnwind l action
  = do uw  <- tc_unwound <$> get
       r   <- action
       uw' <- tc_unwound <$> get
       mapM_ (recordUnwindExpr l) (uw' `diff` uw)
       return r
  where
    diff = deleteFirstsBy ((==) `on` fst3)

-------------------------------------------------------------------------------
-- recordUnwindExpr :: (PP r, F.Reftable r) => SourceSpan -> (Location, Id SourceSpan) -> TCM r ()
-------------------------------------------------------------------------------
recordUnwindExpr l p@(loc, id, θi) 
  = do getUnwound >>= \lst -> if (loc `elem` map fst3 (tracePP "lst" lst)) then tcError l ("Already unwound " ++ loc) else return ()
       -- Sigh, now I see the folly of my naming...
       -- "unwound" is a stack of currently unwound....
       addUnwound p 
       addUnwind >> addAnn (srcPos l) unwindInst 
  where 
    unwindInst = UnwindInst loc id (snd $ toLists θi)
    addUnwind  = modify $ \s -> s {
      tc_unwinds = M.insertWith (flip (++)) l [tracePP "added" (loc,id)`seq`(loc,id)] $ tc_unwinds s
      }

-------------------------------------------------------------------------------
unwindTC :: (PP r, Ord r, F.Reftable r) =>
  RType r -> TCM r (RHeap r, RType r, RSubst r)
-------------------------------------------------------------------------------
unwindTC = go heapEmpty mempty
  where go σ θ' t@(TApp (TDef _) _ _) = do
          (σu, tu, θ'') <- unfoldSafeTC t
          (θ''',_,σu') <- freshHeap σu
          let θ = θ' `mappend` θ'' `mappend` θ'''
              σ' = heapCombine [σu',σ]
          case tu of
            t'@(TApp (TDef _) _ _) -> go σ' θ (apply θ t')
            _                      -> return (σ', apply θ tu, θ)
        go _ _ _ = error "unwind of a non-TDef"

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
       when (l1s /= l2s) $ error "BUG: non-normalized heaps in subHeapM"
       ds <- uncurry subTypesM $ mapPair (readTs $ nub l1s) (σ1, σ2)
       return $ foldl (&*&) EqT ds
  where readTs ls σ = map (flip (heapRead "subHeapM") σ) ls
          
normalizeHeaps γ l σ1 σ2       
  = do castEnvLocs l γ l2s
       return $ mapPair (buildHeap both) (σ1, σ2)
  where
    buildHeap ls σ   = heapFromBinds . filter (flip elem ls.fst) . heapBinds $ σ
    (l1s, both, l2s) = heapSplit σ1 σ2
    
castEnvLocs a γ ls 
  = mapM_ (castLocs ls) xs
    where 
      xs = [ (VarRef a (Id a s),t) | (Id _ s, t) <- envToList γ
                                   , F.symbol s /= returnSymbol
                                   , locs t `intersect` ls /= [] ]
      castLocs ls (e,t) = 
        case filterTypeLs ls t of
          Nothing -> addDeadCast e t
          Just t' -> addDownCast e t t'

filterTypeLs ls t@(TApp (TRef l) _ _)                
  | l `elem` ls = Nothing
  | otherwise   = Just t

filterTypeLs ls t@(TApp TUn ts _)
  = if ts' == [] then Nothing else Just $ mkUnion ts'
  where ts' = [ t | Just t <- filterTypeLs ls <$> ts ]
        
filterTypeLs ls t@(TObj bs r)
  = Just $ TObj [ B b t | (b, Just t) <- zip (b_sym <$> bs) bs' ] r
  where bs' = filterTypeLs ls . b_type <$> bs
        
filterTypeLs _ t = Just $ tracePP "OK" t        

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
  Env (RType r) -> AnnSSA_ r -> RHeap r -> RHeap r -> TCM r ()
--------------------------------------------------------------------------------
castHeapM γ l σ1 σ2
  = do (σ1',σ2') <- normalizeHeaps γ l σ1 σ2
       e <- freshHeapVar l "$$heap"
       subHeapM γ σ1' σ2' >>= go e
  where go e SupT = addDownCastH e σ2
        go e Rel  = addDownCastH e σ2
        go e SubT = addUpCastH e σ2
        go _ EqT  = return ()
        go e Nth  = addDeadCastH e σ2


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
  do  c        <- tc_casts    <$> get
      hc       <- tc_hcasts   <$> get
      winds    <- tc_winds    <$> get
      unwinds  <- tc_unwinds  <$> get
      hexs <- tc_heapexps <$> get
      pgm' <- heapPatchPgm winds unwinds hexs pgm
      return $ fst $ runState (everywhereM' (mkM transform) pgm') (PS c hc)

data PState r = PS { m :: Casts_ r, hm :: HCasts_ r}
type PM     r = State (PState r)

heapPatchPgm winds unwinds hm pgm = 
  return $ fst $ runState (everywhereM' (mkM go) pgm) (HS winds unwinds hm)
  where go :: Statement (AnnSSA_ r) -> HSM r (Statement (AnnSSA_ r))
        go s = do
          wm   <- hs_winds   <$> get
          uwm  <- hs_unwinds <$> get
          expm <- hs_expmap  <$> get
          let l     = getAnnotation $ s
              ws    = lookupStmt l wm
              uws   = lookupStmt l uwm
          modify $ \s -> s { hs_winds   = clearAnnot l wm
                           , hs_unwinds = clearAnnot l uwm
                           , hs_expmap  = clearAnnot l expm
                           }
          return $ case (ws, uws) of
                     ([],[])  -> s
                     ([],uws) -> buildWindCalls True  UnwindAll uws s
                     (ws,[])  -> buildWindCalls True  WindAll   ws  s
                     _        -> error $ errorSameLoc s
        clearAnnot l = M.delete (ann l)
        lookupStmt l = M.findWithDefault [] (ann l)
        errorSameLoc s = (printf "BUG: wind and unwind at %s" (ppshow s))

buildWindCalls pre fn ws s 
  = patchStmt pre windStmts s 
  where 
    display (j,i)             = VarRef l $ Id l (printf "%s ↦ %s" (ppshow j) (ppshow i))
    windStmts                 = [fn l $ map display ws] -- map (buildWind l) ws
    l                         = getAnnotation s
    
patchStmt _   ws (ReturnStmt l e)     = 
  BlockStmt l $ ws ++ [ReturnStmt l e]

patchStmt pre ws (BlockStmt l ss)     = 
  BlockStmt l $ -- if pre then ws ++ ss else
                  ss ++ ws

patchStmt pre ws (IfStmt l e s1 s2)   = 
  IfStmt l e s1 (patchStmt pre ws s2)
                                      
patchStmt pre ws (IfSingleStmt l e s) = 
  IfStmt l e s (BlockStmt l ws)                                      

patchStmt pre ws s                    = 
  BlockStmt (getAnnotation $ tracePP "s" s) $ if tracePP "pre" pre then ws ++[s] else (s:ws)

data HState r = HS { hs_winds   :: !(M.Map SourceSpan [WindCall r])
                   , hs_unwinds :: !(M.Map SourceSpan [(Location, Id SourceSpan)])
                   , hs_expmap  :: !(M.Map SourceSpan [Expression (AnnSSA_ r)]) }
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




