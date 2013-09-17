{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-------------------------------------------------------------------------------------
-- | SSA Monad ----------------------------------------------------------------------
-------------------------------------------------------------------------------------


module Language.Nano.SSA.SSAMonad (
   
   -- * SSA Information
     SsaInfo (..)
   
   -- * SSA Monad
   , SSAM
   , ssaError
   , execute
 
   -- * SSA Environment
   , SsaEnv
   , setSsaEnv
   , getSsaEnv
   , updSsaEnv 
   , extSsaEnv
   , findSsaEnv
 
   -- * Access Annotations
   , addAnn
   , getAnns

   -- * Immutable Variables 
   , isImmutable
   , getImmutables
   , setImmutables
   , addImmutables
   ) where 

import           Control.Applicative                ((<$>))
import           Control.Monad                
import           Control.Monad.State                
import           Control.Monad.Error

import qualified Data.HashMap.Strict as M 
import           Language.Nano.Errors
import           Language.Nano.Env
import           Language.Nano.Types                (dummySpan)
import           Language.Nano.Typecheck.Types
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Parser        (SourceSpan (..))

import           Language.Fixpoint.Misc             
import qualified Language.Fixpoint.Types            as F
import           Text.Printf                        (printf)

-- import           Debug.Trace                        (trace)

type SSAM r     = ErrorT String (State (SsaState r))

data SsaState r = SsaST { immutables :: Env r       -- ^ globals
                        , names      :: SsaEnv      -- ^ current SSA names 
                        , count      :: !Int        -- ^ fresh index
                        , anns       :: !(AnnInfo_ r)    -- ^ built up map of annots 
                        }

type SsaEnv     = Env SsaInfo 
newtype SsaInfo = SI (Id SourceSpan) deriving (Eq)

-------------------------------------------------------------------------------------
extSsaEnv    :: [Id SourceSpan] -> SsaEnv -> SsaEnv 
-------------------------------------------------------------------------------------
extSsaEnv xs = envAdds [(x, SI x) | x <- xs]

-------------------------------------------------------------------------------------
getSsaEnv   :: SSAM r SsaEnv 
-------------------------------------------------------------------------------------
getSsaEnv   = names <$> get 

-------------------------------------------------------------------------------------
addImmutables   :: (F.Reftable r) => Env r -> SSAM r ()
-------------------------------------------------------------------------------------
addImmutables z = modify $ \st -> st { immutables = envExt z (immutables st) } 
  where
    envExt x y  = envFromList $ (envToList x ++ envToList y)

-------------------------------------------------------------------------------------
setImmutables   :: Env r -> SSAM r ()
-------------------------------------------------------------------------------------
setImmutables z = modify $ \st -> st { immutables = z } 

-------------------------------------------------------------------------------------
getImmutables   :: (F.Reftable r) => SSAM r (Env r) 
-------------------------------------------------------------------------------------
getImmutables   = immutables <$> get




-------------------------------------------------------------------------------------
setSsaEnv    :: SsaEnv -> SSAM r () 
-------------------------------------------------------------------------------------
setSsaEnv θ = modify $ \st -> st { names = θ } 


-------------------------------------------------------------------------------------
updSsaEnv   :: SourceSpan -> Id SourceSpan -> SSAM r (Id SourceSpan) 
-------------------------------------------------------------------------------------
updSsaEnv l x 
  = do imm   <- isImmutable x 
       when imm $ ssaError l $ errorWriteImmutable x
       n     <- count <$> get
       let x' = newId l x n
       modify $ \st -> st {names = envAdds [(x, SI x')] (names st)} {count = 1 + n}
       return x'


---------------------------------------------------------------------------------
isImmutable   :: Id SourceSpan -> SSAM r Bool 
---------------------------------------------------------------------------------
isImmutable x = envMem x . immutables <$> get

newId :: SourceSpan -> Id SourceSpan -> Int -> Id SourceSpan 
newId l (Id _ x) n = Id l (x ++ "_SSA_" ++ show n)  

-------------------------------------------------------------------------------
findSsaEnv   :: Id SourceSpan -> SSAM r (Maybe (Id SourceSpan))
-------------------------------------------------------------------------------
findSsaEnv x 
  = do θ  <- names <$> get 
       case envFindTy x θ of 
         Just (SI i) -> return $ Just i 
         Nothing     -> return Nothing 

-- allNames = do xs <- map fst . envToList . names      <$> get
--               ys <- map fst . envToList . immutables <$> get
--               return $ xs ++ ys

-------------------------------------------------------------------------------
addAnn     :: SourceSpan -> Fact_ r -> SSAM r ()
-------------------------------------------------------------------------------
addAnn l f = modify $ \st -> st { anns = inserts l f (anns st) }


-------------------------------------------------------------------------------
getAnns    :: (F.Reftable r) => SSAM r (AnnInfo_ r)
-------------------------------------------------------------------------------
getAnns    = anns <$> get


-------------------------------------------------------------------------------
ssaError       :: SourceSpan -> String -> SSAM r a
-------------------------------------------------------------------------------
ssaError l msg = throwError $ printf "ERROR at %s : %s" (ppshow l) msg


-- inserts l xs m = M.insert l (xs ++ M.lookupDefault [] l m) m

-------------------------------------------------------------------------------
execute         :: SSAM r a -> Either (SourceSpan, String) a 
-------------------------------------------------------------------------------
execute act 
  = case runState (runErrorT act) initState of 
      (Left err, _) -> Left  (dummySpan,  err)
      (Right x, _)  -> Right x

initState :: SsaState r
initState = SsaST envEmpty envEmpty 0 M.empty
