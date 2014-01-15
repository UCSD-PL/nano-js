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
   , tryAction
 
   -- * SSA Environment
   , SsaEnv
   , names
   , updSsaEnv 
   , findSsaEnv
   , extSsaEnv
   , setSsaEnv
   , getSsaEnv
 
   -- * Access Annotations
   , addAnn
   , getAnns

   -- * Tracking Mutability
   , getMutability
   , withMutability

   ) where 

import           Control.Applicative                ((<$>))
import           Control.Monad                
import           Control.Monad.State                
import           Control.Monad.Error hiding (Error)

import           Data.Maybe                         (fromMaybe) 
import qualified Data.HashMap.Strict as M 
import           Language.Nano.Errors
import           Language.Nano.Env
import           Language.Nano.Types                
import           Language.Nano.Typecheck.Types
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Parser.Type   (SourceSpan (..))
import           Language.ECMAScript3.PrettyPrint

import           Language.Fixpoint.Errors
import           Language.Fixpoint.Misc             
import qualified Language.Fixpoint.Types            as F
-- import           Text.Printf                        (printf)

-- import           Debug.Trace                        (trace)

type SSAM r     = ErrorT Error (State (SsaState r))

data SsaState r = SsaST { mutability  :: Env Mutability -- ^ mutability status 
                        , names       :: SsaEnv         -- ^ current SSA names 
                        , count       :: !Int           -- ^ fresh index
                        , anns        :: !(AnnInfo r)   -- ^ built up map of annots 
                        }

type SsaEnv     = Env SsaInfo 
newtype SsaInfo = SI (Id SourceSpan) deriving (Eq)

instance PP SsaInfo where
  pp (SI i) =  pp i


-- -------------------------------------------------------------------------------------
-- withExtSsaEnv    :: [Id SourceSpan] -> SSAM r a -> SSAM r a
-- -------------------------------------------------------------------------------------
-- withExtSsaEnv xs act 
--   = do θ      <- getSsaEnv 
--        let θ'  = envAdds [(x, SI x) | x <- xs] θ
--        modify  $ \st -> st { names = θ' } 
--        r      <- act
--        modify  $ \st -> st { names = θ }
--        return  r

-------------------------------------------------------------------------------------
extSsaEnv    :: [Id SourceSpan] -> SsaEnv -> SsaEnv 
-------------------------------------------------------------------------------------
extSsaEnv xs = envAdds [(x, SI x) | x <- xs]

-------------------------------------------------------------------------------------
getSsaEnv   :: SSAM r SsaEnv 
-------------------------------------------------------------------------------------
getSsaEnv   = names <$> get 

-------------------------------------------------------------------------------------
setSsaEnv    :: SsaEnv -> SSAM r () 
-------------------------------------------------------------------------------------
setSsaEnv θ = modify $ \st -> st { names = θ } 


-------------------------------------------------------------------------------------
withMutability :: Mutability -> [Id SourceSpan] -> SSAM r a -> SSAM r a 
-------------------------------------------------------------------------------------
withMutability m xs act
  = do zOld  <- mutability <$> get
       modify $ \st -> st { mutability = zNew `envUnion` zOld } 
       ret   <- act
       modify $ \st -> st { mutability = zOld }
       return $ ret
    where 
       zNew   = envFromList $ (, m) <$> xs 

---------------------------------------------------------------------------------
getMutability :: Id SourceSpan -> SSAM r Mutability 
---------------------------------------------------------------------------------
getMutability x = (fromMaybe WriteLocal . envFindTy x . mutability) <$> get


-- -------------------------------------------------------------------------------------
-- addImmutables   :: (F.Reftable r) => Env r -> SSAM r ()
-- -------------------------------------------------------------------------------------
-- addImmutables z = modify $ \st -> st { immutables = envExt z (immutables st) } 
--   where
--     envExt x y  = envFromList $ (envToList x ++ envToList y)
-- 
-- -------------------------------------------------------------------------------------
-- setImmutables   :: Env r -> SSAM r ()
-- -------------------------------------------------------------------------------------
-- setImmutables z = modify $ \st -> st { immutables = z } 
-- 
-- -------------------------------------------------------------------------------------
-- getImmutables   :: (F.Reftable r) => SSAM r (Env r) 
-- -------------------------------------------------------------------------------------
-- getImmutables   = immutables <$> get

-------------------------------------------------------------------------------------
updSsaEnv   :: SourceSpan -> Id SourceSpan -> SSAM r (Id SourceSpan) 
-------------------------------------------------------------------------------------
updSsaEnv l x 
  = do mut <- getMutability x
       case mut of
         WriteLocal  -> updSsaEnvLocal l x
         WriteGlobal -> return x
         ReadOnly    -> ssaError $ errorWriteImmutable l x 

updSsaEnvLocal l x 
  = do n     <- count <$> get
       let x' = mkSSAId l x n
       modify $ \st -> st {names = envAdds [(x, SI x')] (names st)} {count = 1 + n}
       return x'

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
addAnn     :: SourceSpan -> Fact r -> SSAM r ()
-------------------------------------------------------------------------------
addAnn l f = modify $ \st -> st { anns = inserts l f (anns st) }


-------------------------------------------------------------------------------
getAnns    :: (F.Reftable r) => SSAM r (AnnInfo r)
-------------------------------------------------------------------------------
getAnns    = anns <$> get


-------------------------------------------------------------------------------
ssaError :: Error -> SSAM r a
-------------------------------------------------------------------------------
ssaError = throwError

-- ssaError e = throwError $ printf "ERROR at %s : %s" (ppshow l) msg


-- inserts l xs m = M.insert l (xs ++ M.lookupDefault [] l m) m

-------------------------------------------------------------------------------
execute         :: SSAM r a -> Either Error a 
-------------------------------------------------------------------------------
execute act 
  = case runState (runErrorT act) initState of 
      (Left err, _) -> Left err
      (Right x, _)  -> Right x

-- Try the action @act@ in the current state. 
-- The state will be intact in the end. Just the result will be returned
tryAction act = get >>= return . runState (runErrorT act)

initState :: SsaState r
initState = SsaST envEmpty envEmpty 0 M.empty

