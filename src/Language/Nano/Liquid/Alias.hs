module Language.Nano.Liquid.Alias (expandAliases) where

import           Data.Maybe
import           Data.Generics.Aliases
import           Data.Generics.Schemes

import           Control.Applicative ((<$>))
import           Control.Monad
import           Control.Monad.State

import           Language.Fixpoint.Errors
import qualified Language.Fixpoint.Types as F

import           Language.ECMAScript3.Syntax.Annotations

import           Language.Nano.Env
import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Typecheck.Types
import qualified Language.Nano.Typecheck.Subst as S
import           Language.Nano.Liquid.Types

expandAliases   :: NanoRefType -> NanoRefType
expandAliases p = expandPred pe' <$> expandRefType (defs p) te' <$> p' 
  where
    p'          = p { pAlias = pe' } {tAlias = te'}
    pe'         = expandPAliasEnv (pAlias p)
    te'         = expandTAliasEnv (defs p) (tAlias p)

------------------------------------------------------------------------------
-- | One-shot expansion for @PAlias@ -----------------------------------------
------------------------------------------------------------------------------

expandPAliasEnv :: PAliasEnv -> PAliasEnv 
expandPAliasEnv pe = solve pe support expandPAlias 
  where
    support        = filter (`envMem` pe) . getPApps . al_body

getPApps       :: F.Pred -> [F.Symbol]
getPApps p     = everything (++) ([] `mkQ` fromP) p
  where 
    fromP (F.PBexp (F.EApp (F.Loc _ f) _)) 
               = [f]
    fromP _    = []

expandPAlias      :: PAliasEnv -> PAlias -> PAlias
expandPAlias pe a = a { al_body = expandPred pe $ al_body a } 


-- expandPred    :: PAliasEnv -> F.Pred -> F.Pred
expandPred pe = everywhere $ mkT $ tx
  where 
    tx p@(F.PBexp (F.EApp f es)) 
              = maybe p (applyPAlias p f es) $ envFindTy f pe
    tx p      = p

applyPAlias p f es a   
  | ne == nx  = F.subst su $ al_body a 
  | otherwise = die $ errorBadPAlias (srcPos f) p nx ne 
  where
    su        = F.mkSubst $ zip xs es
    xs        = al_syvars a
    nx        = length xs
    ne        = length es

-- expandPAliasRefType :: PAliasEnv -> RefType -> RefType
-- expandPAliasRefType = expandPred 

------------------------------------------------------------------------------
-- | One-shot expansion for @TAlias@ -----------------------------------------
------------------------------------------------------------------------------

expandTAliasEnv    :: TDefEnv RefType -> TAliasEnv RefType -> TAliasEnv RefType 
expandTAliasEnv γ te = solve te support $ expandTAlias γ
  where
    support        = filter (`envMem` te) . getTApps γ . al_body

getTApps    :: TDefEnv RefType -> RefType -> [F.Symbol]
getTApps γ  = everything (++) ([] `mkQ` fromT) 
  where
    fromT   :: RefType -> [F.Symbol]
    fromT (TApp (TRef c) _ _) 
            = maybeToList $ findTyId c γ >>= liftM F.symbol . t_name
    fromT _ = []

expandTAlias  :: TDefEnv RefType -> TAliasEnv RefType -> TAlias RefType -> TAlias RefType
expandTAlias γ te a = a {al_body = expandRefType γ te $ al_body a}

expandRefType :: TDefEnv RefType -> TAliasEnv RefType -> RefType -> RefType  
expandRefType γ te = everywhere $ mkT $ tx
  where
    tx t@(TApp (TRef i) ts r) = maybe t (applyTAlias t (pos i) ts r) $ al i
    tx t  = t
    al i  = findTyId i γ >>= liftM F.symbol . t_name >>= (`envFindTy` te)
    pos i = getAnnotation $ fromJust $ t_name $ findTyIdOrDie i γ -- This shouldn't fail

applyTAlias t ss ts_ r a 
  | (nt, ne) == (nα, nx) = (F.subst su $ S.apply θ $ al_body a) `strengthen` r
  | otherwise            = die $ errorBadTAlias ss t nt ne nα nx
  where 
    xs                   = al_syvars a
    αs                   = al_tyvars a
    nx                   = length xs 
    nα                   = length αs 
    ne                   = length es
    nt                   = length ts
    (ts, es)             = splitTsEs ts_
    su                   = F.mkSubst  $ zip xs es
    θ                    = S.fromList $ zip αs ts 

splitTsEs ts       = (ts', [e | TExp e <- es'])
  where
    (ts', es')     = break isExp ts
    isExp (TExp _) = True
    isExp _        = False 

-----------------------------------------------------------------------------
-- | A Generic Solver for Expanding Definitions -----------------------------
-----------------------------------------------------------------------------

solve :: (IsLocated a)
      => Env a              -- ^ Input definitions
      -> (a -> [F.Symbol])  -- ^ Dependencies (each Symbol is in `defs`)
      -> (Env a -> a -> a)  -- ^ Expansion function
      -> Env a              -- ^ Output "closed" definitions

solve defs deps exp = ex_solved $ snd $ runState act st0
  where 
    st0             = ExS defs envEmpty
    xs              = [x `at` d | (x, d) <- envToList defs]
    act             = forM_ xs $ solveM deps exp []


solveM deps exp stk x 
  | x `elem` stk    = die $ errorCyclicDefs (srcPos x) x stk
  | otherwise       = do xr <- getResult x
                         case xr of
                           Just d' -> return (x, d') 
                           Nothing -> do d      <- getDefinition x
                                         let ys  = [ y `at` d | y <- deps d]
                                         yds'   <- mapM (solveM deps exp (x:stk)) ys 
                                         setResult x $ exp (envFromList yds') d

type ExM a     = State (ExState a)

data ExState a = ExS { ex_defs   :: Env a
                     , ex_solved :: Env a 
                     }

-- getDefinition   :: F.Symbol -> ExM a a
getDefinition x = (fromMaybe (die $ bugUnknownAlias (srcPos x) x) . envFindTy (val x) . ex_defs) <$> get

-- getResult     :: F.Symbol -> ExM a (Maybe a)
getResult x   = (envFindTy (val x) . ex_solved) <$> get  

setResult     :: (IsLocated a) => Located F.Symbol -> a -> ExM a (Located F.Symbol, a)
setResult x d = do modify $ \st -> st { ex_solved = envAdd x d (ex_solved st) } 
                   return (x, d)


at x d        = Loc (srcPos d) (F.symbol x)