module Language.Nano.Liquid.Alias (expandAliases) where

import           Data.Maybe
import           Data.Generics.Aliases
import           Data.Generics.Schemes

import           Control.Applicative ((<$>))
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Error hiding (Error)
import           Text.Printf 

import           Language.Fixpoint.Errors
import qualified Language.Fixpoint.Types as F

import           Language.Nano.Env
import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Typecheck.Types
import           Language.Nano.Liquid.Types

expandAliases :: NanoRefType -> NanoRefType
expandAliases p = expandRefType te' p' 
  where
    p'          = p { pAlias = pe' } {tAlias = te'}
    pe'         = expandPAliasEnv                              $ pAlias p
    te'         = expandTAliasEnv $ expandPAliasesTAliases pe' $ tAlias p

---------------------------------------------------------------------------------------
-- | One-shot expansion for @PAlias@ -------------------------------------------------- 
---------------------------------------------------------------------------------------

expandPAliasEnv :: PAliasEnv -> PAliasEnv 
expandPAliasEnv pe = solve pe support expandPAlias 
  where
    support        = filter isAlias . getApps . al_body
    isAlias x      = x `envMem` pe
    getApps        :: F.Pred -> [F.Symbol]
    getApps p      = everything (++) ([] `mkQ` fromP) p
    fromP (F.PBexp (F.EApp (F.Loc _ f) _)) = [f]
    fromP _                                = []


expandPAlias  :: PAliasEnv -> PAlias -> PAlias
expandPAlias  = undefined

expandPred    :: PAliasEnv -> F.Pred -> F.Pred
expandPred    = undefined

---------------------------------------------------------------------------------------
-- | One-shot expansion for @TAlias@ -------------------------------------------------- 
---------------------------------------------------------------------------------------

expandTAliasEnv  :: TAliasEnv RefType -> TAliasEnv RefType 
expandTAliasEnv  = undefined

expandTAlias :: TAliasEnv RefType -> TAlias RefType -> TAlias RefType
expandTAlias = undefined

expandRefType :: TAliasEnv RefType -> RefType -> RefType  
expandRefType = undefined

expandPAliasesTAliases :: PAliasEnv -> TAliasEnv RefType -> TAliasEnv RefType
expandPAliasesTAliases = undefined

---------------------------------------------------------------------------------------
-- | A Generic Solver for Expanding Definitions --------------------------------------- 
---------------------------------------------------------------------------------------

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
