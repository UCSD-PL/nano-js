{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Nano.Typecheck.Typecheck (verifyFile, typeCheck, patchTypeAnnots) where 

import           Control.Exception                  (throw)
import           Control.Applicative                ((<$>))
import           Control.Monad                

import qualified Data.HashSet                       as HS 
import qualified Data.HashMap.Strict                as M 
import qualified Data.Traversable                   as T
import qualified Data.Either                        as E
import           Data.Monoid
import qualified Data.Foldable                      as FL
import qualified Data.List                          as L
import           Data.Maybe                         (catMaybes, isJust, fromJust, fromMaybe, listToMaybe, maybeToList)
import           Data.Generics                   

import           Text.PrettyPrint.HughesPJ          (text, render, vcat, ($+$), (<+>))
import           Text.Printf                        (printf)

import           Language.Nano.CmdLine              (getOpts)
import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Annots
import           Language.Nano.Env
import           Language.Nano.Misc
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Parse 
import           Language.Nano.Typecheck.TCMonad
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Lookup
import           Language.Nano.Typecheck.Unfold
import           Language.Nano.Typecheck.Unify
import           Language.Nano.SSA.SSA

import           Language.Fixpoint.Errors
import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc             as FM 
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser.Type  (SourceSpan (..))
import           Debug.Trace                        hiding (traceShow)

import qualified System.Console.CmdArgs.Verbosity as V


--------------------------------------------------------------------------------
-- | Top-level Verifier 

--------------------------------------------------------------------------------
verifyFile :: FilePath -> IO (UAnnSol a, F.FixResult Error)
--------------------------------------------------------------------------------
verifyFile f = do 
  p <- parseNanoFromFile f
  case p of 
    Left err -> return (NoAnn, F.Unsafe [err]) 
    Right nano -> 
      do  V.whenLoud $ donePhase FM.Loud "Parse"
          V.whenLoud $ putStrLn . render . pp $ nano
          case ssaTransform' nano of 
            Left err -> return (NoAnn, F.Unsafe [err])
            Right p  -> 
              do 
                let nanoSsa = patchTypeAnnots p
                V.whenLoud  $ donePhase FM.Loud "SSA Transform"
                V.whenLoud  $ putStrLn . render . pp $ p
                verb       <- V.getVerbosity
                let annp    = execute verb nanoSsa $ tcNano p
                r          <- either unsafe safe annp 
                V.whenLoud  $ donePhase FM.Loud "Typechecking"
                return      $ (NoAnn, r)

unsafe errs = do putStrLn "\n\n\nErrors Found!\n\n" 
                 forM_ errs (putStrLn . ppshow) 
                 return $ F.Unsafe errs

safe (_, Nano {code = Src fs})
  = do V.whenLoud $ printAllAnns fs 
       nfc       <- noFailCasts <$> getOpts
       return     $ F.Safe `mappend` failCasts nfc fs 


-- | Inline type annotations
patchTypeAnnots :: (PP r, F.Reftable r) => NanoSSAR r -> NanoTSSAR r
patchTypeAnnots p@(Nano {code = Src fs, specs = m, chSpecs = cm }) = 
    p {code = Src $ (patchAnn <$>) <$> fs}
  where
    patchAnn (Ann l bs) = Ann l $ (TAnnot <$> (maybeToList $ M.lookup l mm)) ++ bs
    mm = M.fromList (mapFst getAnnotation <$> envToList m ++ envToList cm)


-- | Cast manipulation

failCasts True  _  = F.Safe
failCasts False fs = applyNonNull F.Safe F.Unsafe $ concatMap castErrors $ getCasts fs 

getCasts         :: (Data r, Typeable r) => [Statement (AnnType r)] -> [(AnnType r)]
getCasts stmts   = everything (++) ([] `mkQ` f) stmts
  where 
    f            :: Expression (AnnType r) -> [(AnnType r)]
    f (Cast a _) = [a]
    f _          = [] 

-- castErrors :: (F.Reftable r) => AnnType r -> [Error] 
castErrors (Ann l facts) = downErrors ++ deadErrors
  where 
    downErrors           = [errorDownCast l t | TCast _ (DCST t) <- facts]
    deadErrors           = [errorDeadCast l   | TCast _ (DC _)   <- facts]

printAllAnns fs 
  = do putStrLn "********************** ALL ANNOTATIONS **********************"
       forM_ fs $ T.mapM printAnn 
    where 
       printAnn (Ann _ []) = return () 
       printAnn (Ann l fs) = putStrLn $ printf "At %s: %s" (ppshow l) (ppshow fs)


-------------------------------------------------------------------------------------------
typeCheck :: (Data r, Ord r, PP r, F.Reftable r, Substitutable r (Fact r), Free (Fact r)) 
          => V.Verbosity -> (NanoSSAR r) -> Either [Error] (NanoTypeR r)
-------------------------------------------------------------------------------------------
typeCheck verb pgm = fmap snd (execute verb pgm $ tcNano pgm)

-------------------------------------------------------------------------------
-- | TypeCheck Nano Program ---------------------------------------------------
-------------------------------------------------------------------------------
tcNano :: (Data r, Ord r, PP r, F.Reftable r, Substitutable r (Fact r), Free (Fact r)) 
            => NanoSSAR r -> TCM r (AnnInfo r, NanoTypeR r)
-------------------------------------------------------------------------------
tcNano p@(Nano {code = Src fs})
  = do checkTypeDefs p
       (fs', γo) <- tcInScope γ $ tcStmts γ fs
       m         <- concatMaps <$> getAllAnns
       θ         <- getSubst
       let p1     = p {code = (patchAnn m . apply θ) <$> Src fs'}
       whenLoud   $ (traceCodePP p1 m θ)
       case γo of 
         Just γ'  -> do  mc    <- mCls $ envIds $ tce_cls γ'
                         let p2 = p1 { chSpecs = envUnion mc (chSpecs p1) }
                         return $ (m, p2)
         Nothing  -> error "BUG:tcNano should end with an environment"
    where
       γ         = initEnv p
       -- A mapping from class names to the recovered types.
       mCls ks   = envFromList . catMaybes <$> mapM gs ks
       gs k      =  do  s <- getSpecM k 
                        case s of 
                          Just t  -> return $ Just (k,t)
                          Nothing -> return $ Nothing

patchAnn m (Ann l fs) = Ann l $ sortNub $ fs'' ++ fs' ++ fs 
  where
    fs'               = [f | f@(TypInst _ _) <- M.lookupDefault [] l m]
    fs''              = [f | f@(Overload (Just _)) <- M.lookupDefault [] l m]

-- Initalize the environment with all the available specs!
initEnv pgm           = TCE (envUnion (specs pgm) (chSpecs pgm)) (chSpecs pgm) 
                            classEnv emptyContext
  where classEnv      = envFromList [ (s, ClassStmt l s e i b) | let Src ss = code pgm
                                                               , ClassStmt l s e i b <- ss ]

traceCodePP p m s     = trace (render $ {- codePP p m s -} pp p) $ return ()
      
codePP (Nano {code = Src src}) anns sub 
  =   text "*************************** CODE ****************************************"
  $+$ pp src
  $+$ text "*************************** SUBSTITUTIONS *******************************"
  $+$ pp sub
  $+$ text "*************************** ANNOTATIONS **********************************"
  $+$ vcat (pp <$> {- annotCasts -} M.toList anns )
  $+$ text "*************************************************************************"

annotCasts anns = [ (l, f) | (l, fs) <- M.toList anns, f@(TCast _ _) <- fs]

-------------------------------------------------------------------------------
checkTypeDefs :: (Data r, Typeable r, F.Reftable r) => Nano (AnnSSA r) (RType r) -> TCM r ()
-------------------------------------------------------------------------------
checkTypeDefs pgm = reportAll $ grep
  where 
    ds        = specs pgm 
    ts        = defs pgm
    reportAll = mapM_ report
    report t  = tcError $ errorUnboundType (srcPos t) t
    -- There should be no undefined type constructors
    grep :: [Id SourceSpan]        = everything (++) ([] `mkQ` g) ds
    g (TDef i) | not $ envMem i ts = [i]
    g _                            = [ ]
    -- TODO: Also add check for free top-level type variables, i.e. make sure 
    -- all type variables used are bound. Use something like:
    -- @everythingWithContext@



-------------------------------------------------------------------------------
-- | Typecheck Environment ----------------------------------------------------
-------------------------------------------------------------------------------

--   We define this alias as the "output" type for typechecking any entity
--   that can create or affect binders (e.g. @VarDecl@ or @Statement@)
--   @Nothing@ means if we definitely hit a "return" 
--   @Just γ'@ means environment extended with statement binders


data TCEnv r  = TCE { tce_env  :: Env (RType r)
                    -- ^ Program specs. Includes functions and class types
                    -- _after_ they have been computed.
                    , tce_spec :: Env (RType r)               
                    , tce_cls  :: Env (Statement (AnnSSA r))  -- ^ Class definitions
                    , tce_ctx  :: !IContext 
                    }

type TCEnvO r = Maybe (TCEnv r)

instance (PP r, F.Reftable r) => Substitutable r (TCEnv r) where 
  apply θ (TCE m sp cl c) = TCE (apply θ m) (apply θ sp) cl c 
  -- Not doing the application on the class env

instance (PP r, F.Reftable r) => PP (TCEnv r) where
  pp = ppTCEnv

ppTCEnv (TCE env spc _ ctx) 
  =   text "******************** Environment ************************"
  $+$ pp env
  $+$ text "******************** Specifications *********************"
  $+$ pp spc 
  $+$ text "******************** Call Context ***********************"
  $+$ pp ctx


tcEnvPushSite i γ            = γ { tce_ctx = pushContext i    $ tce_ctx γ }

-- Since we assume the raw types should be the same among the various SSA 
-- variants, we should only be adding bindings for the non-SSA version of the 
-- variable, to be able to retrieve it correctly later on.
tcEnvAdds                   :: (IsLocated a, F.Reftable r) => [(Id a, RType r)] -> TCEnv r -> TCEnv r
tcEnvAdds     x γ            = γ { tce_env = envAdds (mapFst stripSSAId <$> x)        $ tce_env γ }

tcEnvAddReturn x t γ         = γ { tce_env = envAddReturn x t $ tce_env γ }
tcEnvMem x                   = envMem (stripSSAId x)      . tce_env 
tcEnvFindTy x                = envFindTy (stripSSAId x)   . tce_env
tcEnvFindReturn              = envFindReturn              . tce_env

tcEnvFindSpec x              = envFindTy (stripSSAId x)   . tce_spec 
tcEnvFindSpecOrTy x γ        = msum [tcEnvFindTy x γ, tcEnvFindSpec x γ]
tcEnvFindSpecOrDie x         = fromMaybe ugh              . tcEnvFindSpec x  
  where ugh                  = die $ errorUnboundId (ann $ getAnnotation x) x

tcEnvFindCls x               = envFindTy x                . tce_cls
tcEnvFindClsOrDie x          = fromMaybe ugh              . tcEnvFindCls x  
  where ugh                  = die $ errorUnboundId (ann $ getAnnotation x) x

tcEnvFindTyOrDie l x         = fromMaybe ugh . tcEnvFindTy (stripSSAId x)  where ugh = die $ errorUnboundId (ann l) x


-------------------------------------------------------------------------------
-- | TypeCheck Scoped Block in Environment ------------------------------------
-------------------------------------------------------------------------------

tcInScope γ act = accumAnn annCheck act
  where
    annCheck    = catMaybes . map (validInst γ) . M.toList

-------------------------------------------------------------------------------
-- | TypeCheck Function -------------------------------------------------------
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
tcFun :: (Ord r, F.Reftable r, PP r) =>
  TCEnv r -> Statement (AnnSSA r) -> TCM r (Statement (AnnSSA r), Maybe (TCEnv r))
-------------------------------------------------------------------------------
tcFun γ (FunctionStmt l f xs body)
  = case tcEnvFindTy f γ of
      Nothing -> die $ errorMissingSpec (srcPos l) f
      Just ft -> do body' <- foldM (tcFun1 γ l f xs) body =<< tcFunTys l f xs ft
                    return   (FunctionStmt l f xs body', Just γ) 
tcFun _  s = die $ bug (srcPos s) $ "Calling tcFun not on FunctionStatement"

-------------------------------------------------------------------------------
tcFun1 ::
  (Ord r, F.Reftable r, PP r, IsLocated a1, IsLocated t1, IsLocated a, CallSite t) =>
  TCEnv r -> a -> t1 -> [Id a1] -> [Statement (AnnSSA r)] -> 
  (t, ([TVar], [RType r], RType r)) -> TCM r [Statement (AnnSSA r)]
-------------------------------------------------------------------------------
tcFun1 γ l f xs body (i, (αs,ts,t)) = tcInScope γ' $ tcFunBody γ' l body t
  where 
    γ'                              = envAddFun f i αs xs ts t γ 

tcFunBody γ l body t = liftM2 (,) (tcStmts γ body) getTDefs >>= ret
  where
    ret ((_, Just _), d) | not (isSubType d t tVoid) = tcError $ errorMissingReturn (srcPos l)
    ret ((b, _     ), _) | otherwise                 = return b

-------------------------------------------------------------------------------
envAddFun :: (F.Reftable r, IsLocated c, IsLocated a, CallSite b) =>
  a -> b -> [TVar] -> [Id c] -> [RType r] -> RType r -> TCEnv r -> TCEnv r
-------------------------------------------------------------------------------
envAddFun f i αs xs ts t = tcEnvAdds tyBinds 
                         . tcEnvAdds (varBinds xs ts) 
                         . tcEnvAddReturn f t
                         . tcEnvPushSite i 
  where  
    tyBinds                = [(tVarId α, tVar α) | α <- αs]
    varBinds               = zip
    
validInst γ (l, ts)
  = case [β | β <-  HS.toList $ free ts, not ((tVarId β) `tcEnvMem` γ)] of
      [] -> Nothing
      βs -> Just $ errorFreeTyVar l βs

-- | Strings ahead: HACK Alert
tVarId (TV a l) = Id l $ "TVAR$$" ++ F.symbolString a   


---------------------------------------------------------------------------------------
tcClassElt :: (Ord r, PP r, F.Reftable r) 
          => TCEnv r -> Id (AnnSSA r) -> ClassElt (AnnSSA r) -> TCM r (ClassElt (AnnSSA r))
---------------------------------------------------------------------------------------
-- TODO: Force void return type for constructor.
tcClassElt γ id (Constructor l xs body) = tcClassEltAux l id f 
  where f ft  =     tcFunTys l id xs ft 
                >>= foldM (tcFun1 γ l id xs) body 
                >>= return . Constructor l xs
        id    = Id l "constructor"

-- The type annotation in variable members is in the VarDecl part so we can use
-- normal tcVarDecl for that part.
-- TODO: perhaps we don't need private members to be annotated, since they do
-- not contribute to the type of the class.
tcClassElt γ id (MemberVarDecl l m s v) = tcClassEltAux (getAnnotation v) id f
    where f _ = tcVarDecl γ v >>= return . MemberVarDecl l m s . fst

tcClassElt γ id (MemberMethDecl l m s i xs body) = 
  tcClassEltAux l i $ 
    \ft -> do body'  <- foldM (tcFun1 γ l i xs) body =<< tcFunTys l i xs ft
              return  $ MemberMethDecl l m s i xs body'

tcClassEltAux l id f = 
  case [ t | TAnnot t  <- ann_fact l ] of 
    [  ]  -> tcError    $ errorConstAnnMissing (srcPos l) id
    [ft]  -> f ft 
    _     -> error      $ "tcClassEltType:multi-type constructor"

--------------------------------------------------------------------------------
tcSeq :: (TCEnv r -> a -> TCM r (b, TCEnvO r)) -> TCEnv r -> [a] -> TCM r ([b], TCEnvO r)
--------------------------------------------------------------------------------
tcSeq f             = go []
  where
    go acc γ []     = return (reverse acc, Just γ)
    go acc γ (x:xs) = do (y, γo) <- f γ x
                         case γo of
                           Nothing -> return (reverse (y:acc), Nothing) 
                           Just γ' -> go (y:acc) γ' xs

--------------------------------------------------------------------------------
tcStmts :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact r), Free (Fact r)) =>
            TCEnv r -> [Statement (AnnSSA r)] -> TCM r ([Statement (AnnSSA r)], TCEnvO r)
--------------------------------------------------------------------------------
tcStmts γ stmts 
  = do γ' <- addStatementFunBinds γ stmts
       tcSeq tcStmt γ' stmts

addStatementFunBinds γ stmts 
  = do fts   <- forM fns $ \f -> (f,) <$> getSpecOrDie f
       return $ tcEnvAdds fts γ
    where
       fs  = concatMap getFunctionStatements stmts
       fns = [f | FunctionStmt _ f _ _ <- fs]

-------------------------------------------------------------------------------
tcStmt  :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact r), Free (Fact r)) =>
            TCEnv r -> Statement (AnnSSA r) -> TCM r (Statement (AnnSSA r), TCEnvO r)
-------------------------------------------------------------------------------
-- skip
tcStmt γ s@(EmptyStmt _) 
  = return (s, Just γ)

-- x = e
tcStmt γ (ExprStmt l1 (AssignExpr l2 OpAssign (LVar lx x) e))   
  = do (e', g) <- tcAsgn l1 γ (Id lx x) e
       return   (ExprStmt l1 (AssignExpr l2 OpAssign (LVar lx x) e'), g)

-- e1.fld = e2
tcStmt γ (ExprStmt l (AssignExpr l2 OpAssign (LDot l1 e1 fld) e2))
  = do (e1', tfld) <- tcPropRead getProp γ l e1 fld
       (e2', t2)   <- tcExpr γ $ e2                    
       e2''        <- castM  ξ e2' t2 tfld
       return         (ExprStmt l (AssignExpr l2 OpAssign (LDot l1 e1' fld) e2''), Just γ)
    where
       ξ            = tce_ctx γ

-- e
tcStmt γ (ExprStmt l e)   
  = do (e', _) <- tcExpr γ e 
       return (ExprStmt l e', Just γ) 

-- s1;s2;...;sn
tcStmt γ (BlockStmt l stmts) 
  = do (stmts', z) <- tcStmts γ stmts
       return (BlockStmt l stmts', z)

-- if b { s1 }
tcStmt γ (IfSingleStmt l b s)
  = tcStmt γ (IfStmt l b s (EmptyStmt l))

-- if b { s1 } else { s2 }
tcStmt γ (IfStmt l e s1 s2)
  = do (e', t)   <- tcExpr γ e 
       unifyTypeM (srcPos l) "If condition" e t tBool
       (s1', γ1) <- tcStmt γ s1
       (s2', γ2) <- tcStmt γ s2
       z         <- envJoin l γ γ1 γ2
       return       (IfStmt l e' s1' s2', z)

-- while c { b } ; exit environment is entry as may skip. SSA adds phi-asgn prior to while.
tcStmt γ (WhileStmt l c b) 
  = do (c', t)   <- tcExpr γ c
       unifyTypeM (srcPos l) "While condition" c t tBool
       (b', _)   <- tcStmt γ' b
       return       (WhileStmt l c' b', Just γ)  
    where 
       xts'       = [(mkNextId x, tcEnvFindTyOrDie l x γ) | x <- phiVarsAnnot l]
       γ'         = tcEnvAdds xts' γ

-- var x1 [ = e1 ]; ... ; var xn [= en];
tcStmt γ (VarDeclStmt l ds)
  = do (ds', z) <- tcSeq tcVarDecl γ ds
       return      (VarDeclStmt l ds', z)

-- return e 
tcStmt γ (ReturnStmt l eo) 
  = do  (eo', t)    <- case eo of 
                         Nothing -> return (Nothing, tVoid)
                         Just e  -> mapFst Just <$>  tcExpr γ e
        let rt       = tcEnvFindReturn γ 
        θ           <- unifyTypeM (srcPos l) "Return" eo t rt
        -- Apply the substitution
        let (rt',t') = mapPair (apply θ) (rt,t)
        -- Subtype the arguments against the formals and cast using subtyping result
        eo''        <- case eo' of
                        Nothing -> return Nothing
                        Just e' -> Just <$> castM (tce_ctx γ) e' t' rt'
        return (ReturnStmt l eo'', Nothing)

tcStmt γ s@(FunctionStmt _ _ _ _)
  = tcFun γ s

-- class A [extends B] [implements I,J,...] { ... }
tcStmt γ c@(ClassStmt l i e is ce)
  = do  t     <- classType γ c
        ce'   <- tcWithThis t $ mapM (tcClassElt γ i) ce
        return $ (ClassStmt l i e is ce', Just γ)

-- OTHER (Not handled)
tcStmt _ s 
  = convertError "tcStmt" s


-- Extract the type of a class from its definition using the annotations of its
-- fields.
---------------------------------------------------------------------------------------
classType :: (Ord r, PP r, F.Reftable r) 
          => TCEnv r -> Statement (AnnSSA r) -> TCM r (RType r)
---------------------------------------------------------------------------------------
classType γ (ClassStmt l id (Just parent) _ cs) =
  do
    θ   <- getTDefs
    -- Try to find the parent class in the env. If this fails, 
    -- compute it on the fly
    TObj bs _ <- findClassSpec γ parent
    bs' <- foldM (addField θ) bs $ classEltType <$> cs
    addCTToSpec id $ TObj bs' fTop
  where
    addField θ bs (B s t) = 
      let m = M.fromList (p <$> bs) in
      case M.lookup s m of
        Just t0 | equiv θ t0 t -> return  $ u <$> M.toList (M.insert s t m)
        Just t0 | otherwise    -> tcError $ errorClassExtends (srcPos l) id parent s
        Nothing                -> return   $ u <$> M.toList (M.insert s t m)
    es (B s _) s' = s == s'
    p  (B s t)    = (s, t)
    u  (s, t)     = B s t

classType _ (ClassStmt l id Nothing _ cs) =
  addCTToSpec id $ TObj (classEltType <$> cs) fTop

addCTToSpec i t = addSpec i t >> return t

-- There are two ways to get a class spec (type):
-- ∙ Look in tc_spec (part fo the TCM state)
-- ∙ Compute it from the source definition of the class,
--   store it in the monad and return it  
---------------------------------------------------------------------------------------
findClassSpec :: (Ord r, PP r, F.Reftable r) => TCEnv r -> Id (AnnSSA r) -> TCM r (RType r)  
---------------------------------------------------------------------------------------
findClassSpec γ x = getSpecM x >>= go
  where go (Just t) = return t
        go Nothing  = classType γ (tcEnvFindClsOrDie x γ)

---------------------------------------------------------------------------------------
classEltType :: (Ord r, PP r, F.Reftable r) => ClassElt (AnnSSA r) -> Bind r
---------------------------------------------------------------------------------------
classEltType (Constructor l _ _ )                   = classEltToBind l "constructor"
classEltType (MemberVarDecl _ _ _ (VarDecl l v _))  = classEltToBind l v
classEltType (MemberMethDecl  l _ _ i _ _ )         = classEltToBind l i

classEltToBind l s = 
  case [ t | TAnnot t <- ann_fact l ] of 
    [ ] -> error "classEltType:no-type-annotation"
    [t] -> B (F.symbol s) t
    _   -> error "classEltType:non-singleton type"


---------------------------------------------------------------------------------------
tcVarDecl :: (Ord r, PP r, F.Reftable r) 
          => TCEnv r -> VarDecl (AnnSSA r) -> TCM r (VarDecl (AnnSSA r), TCEnvO r)
---------------------------------------------------------------------------------------
tcVarDecl γ v@(VarDecl l x (Just e)) 
  = do (e', g) <- tcAsgn l γ x e
       return (VarDecl l x (Just e'), g)

tcVarDecl γ v@(VarDecl l x Nothing) =
  case [ t | TAnnot t <- ann_fact l ] of 
    [ ] -> tcError $ errorVarDeclAnnot (srcPos l) x 
    [t] -> return (v, Just $ tcEnvAdds [(x, t)] γ)
    _   -> error "tcVarDecl:multiple type annotation"

-------------------------------------------------------------------------------
tcAsgn :: (PP r, Ord r, F.Reftable r) => 
  AnnSSA r -> TCEnv r -> Id (AnnSSA r) -> ExprSSAR r -> TCM r (ExprSSAR r, TCEnvO r)
-------------------------------------------------------------------------------
tcAsgn l γ x e
  = do (e' , t) <- tcExprT γ e rhsT
       return      (e', Just $ tcEnvAdds [(x, t)] γ)
    where
    -- Where to look for an annotation?
    -- ∙ At the current AST node (for VarDecl)
    -- ∙ The spec environment - for annotated declared variables.
       rhsT      = msum [tcEnvFindSpecOrTy x γ, listToMaybe [ t | TAnnot t <- ann_fact l ]]


-------------------------------------------------------------------------------
tcExprT :: (Ord r, PP r, F.Reftable r)
       => TCEnv r -> ExprSSAR r -> Maybe (RType r) -> TCM r (ExprSSAR r, RType r)
-------------------------------------------------------------------------------
tcExprT γ e to 
  = do (e', t)    <- tcExpr γ e
       (e'', te)  <- case to of
                       Nothing -> return (e', t)
                       Just ta -> (,ta) <$> castM (tce_ctx γ) e t ta
                    {-Just ta -> checkAnnotation "tcExprT" e t ta-}
       return     (e'', te)

----------------------------------------------------------------------------------------------
tcExpr :: (Ord r, PP r, F.Reftable r) => TCEnv r -> ExprSSAR r -> TCM r (ExprSSAR r, RType r)
----------------------------------------------------------------------------------------------
tcExpr _ e@(IntLit _ _)
  = return (e, tInt)

tcExpr _ e@(BoolLit _ _)
  = return (e, tBool)

tcExpr _ e@(StringLit _ _)
  = return (e, tString)

tcExpr _ e@(NullLit _)
  = return (e, tNull)

tcExpr _ e@(ThisRef _)
  = (e,) <$> tcPeekThis

tcExpr γ e@(VarRef l x)
  = return (e, tcEnvFindTyOrDie l x γ) 
  
  -- case tcEnvFindTy x γ of 
  --     -- Nothing -> die $ errorUnboundId (ann l) x
  --     Nothing -> die $ errorUnboundIdEnv (ann l) x (tce_env γ)
  --     Just z  -> return $ (e, z)

tcExpr γ e@(PrefixExpr _ _ _)
  = tcCall γ e 

tcExpr γ e@(InfixExpr _ _ _ _)
  = tcCall γ e 

tcExpr γ e@(CallExpr _ _ _)
  = tcCall γ e 

tcExpr γ e@(ArrayLit _ _)
  = tcCall γ e 

tcExpr γ (ObjectLit l bs) 
  = do let (ps, es)  = unzip bs
       ets          <- mapM (tcExpr γ) es
       let (es', ts) = unzip ets
       let bts       = zipWith B (F.symbol <$> ps) ts
       return (ObjectLit l (zip ps es'), TObj bts fTop)

tcExpr γ (Cast l@(Ann loc fs) e)
  = do (e', t) <- tcExpr γ e
       case e' of
         Cast (Ann _ fs') e'' -> return (Cast (Ann loc (fs ++ fs')) e'', t)
         _                    -> return (Cast l e', t)

-- e.f
tcExpr γ e1@(DotRef l e fld) 
  = do (e', t) <- tcPropRead getProp γ l e (unId fld)
       return     (DotRef l e' fld, t)
        
-- e["f"]
tcExpr γ (BracketRef l e fld@(StringLit _ s)) 
  = do (e', t) <- tcPropRead getProp γ l e s
       return     (BracketRef l e' fld, t)
 
-- e1[e2]
tcExpr γ e@(BracketRef _ _ _) 
  = tcCall γ e

-- e1[e2] = e3
tcExpr γ e@(AssignExpr _ OpAssign (LBracket _ _ _) _)
  = tcCall γ e

-- new C(e, ...)
-- C is required to be a class name
-- TODO: Polymorphic instantiations!!!
tcExpr γ e@(NewExpr _ _ _) 
  = tcCall γ e

tcExpr _ e 
  = convertError "tcExpr" e

---------------------------------------------------------------------------------------
tcCall :: (Ord r, F.Reftable r, PP r) => TCEnv r -> ExprSSAR r -> TCM r (ExprSSAR r, RType r)
---------------------------------------------------------------------------------------

-- | `o e`
tcCall γ ex@(PrefixExpr l o e)        
  = do z                      <- tcCallMatch γ l o [e] (prefixOpTy o $ tce_env γ) 
       case z of
         Just ([e'], t)       -> return (PrefixExpr l o e', t)
         Nothing              -> deadCast (srcPos l) γ ex 

-- | `e1 o e2`
tcCall γ ex@(InfixExpr l o e1 e2)        
  = do z                      <- tcCallMatch γ l o [e1, e2] (infixOpTy o $ tce_env γ) 
       case z of
         Just ([e1', e2'], t) -> return (InfixExpr l o e1' e2', t)
         Nothing              -> deadCast (srcPos l) γ ex 
         
-- | `e(e1,...,en)`
tcCall γ ex@(CallExpr l e es)
  = do (e', ft0)              <- tcExpr γ e
       z                      <- tcCallMatch γ l e es ft0
       case z of
         Just (es', t)        -> return (CallExpr l e' es', t)
         Nothing              -> deadCast (srcPos l) γ ex

-- | `e1[e2]`
tcCall γ ex@(BracketRef l e1 e2)
  = do z                      <- tcCallMatch γ l BIBracketRef [e1, e2] $ builtinOpTy l BIBracketRef $ tce_env γ 
       case z of
         Just ([e1', e2'], t) -> return (BracketRef l e1' e2', t)
         Nothing              -> tcError $ errorPropRead (srcPos l) e1 e2 
                                 -- deadCast (srcPos l) γ ex 
   

-- | `e1[e2] = e3`
tcCall γ ex@(AssignExpr l OpAssign (LBracket l1 e1 e2) e3)
  = do z                           <- tcCallMatch γ l BIBracketAssign [e1,e2,e3] $ builtinOpTy l BIBracketAssign $ tce_env γ
       case z of
         Just ([e1', e2', e3'], t) -> return (AssignExpr l OpAssign (LBracket l1 e1' e2') e3', t)
         Nothing                   -> tcError $ errorBracketAssign (srcPos l) ex 


tcCall γ ex@(ArrayLit l es) 
  = do z                           <- tcCallMatch γ l BIArrayLit es $ arrayLitTy l (length es) $ tce_env γ
       case z of
         Just (es', t)             -> return (ArrayLit l es', t)
         Nothing                   -> tcError $ errorArrayLit (srcPos l) ex

tcCall γ ex@(NewExpr l (VarRef lv id) es)
  = do  t     <- findClassSpec γ id
        tdefs <- getTDefs 
        return undefined
        case getProp l (tce_env γ) tdefs "constructor" t of
          Just (_,tc)  -> do
            when (not $ isTFun tc) $ tcError $ errorConstNonFunc (srcPos l) id 
            z <- tcCallMatch γ l "constructor" es tc
            case z of
              Just (es', _) -> return (NewExpr l (VarRef lv id) es', t)
              -- Constructor's return type is void - instead return the class type
              Nothing              -> deadCast (srcPos l) γ ex 

tcCall γ e
  = die $ bug (srcPos e) $ "tcCall: cannot handle" ++ ppshow e        


tcCallMatch γ l fn es ft0
  = do  (es', ts)     <- unzip <$> mapM (tcExpr γ) es
        case calleeType l ts ft0 of 
          -- Try to match it with a non-generic type
          Just t -> call es' ts t
          -- If this fails, try to instantiate possible generic types found
          -- in the function signature.
          Nothing ->
            do  mType <- resolveOverload γ l fn es' ts ft0
                addAnn (srcPos l) (Overload mType)
                maybe (return Nothing) (call es' ts) mType
    where
      call es' ts t = fmap Just $ tcCallCase γ l fn es' ts t


resolveOverload γ l fn es ts ft =
  shd <$> filterM (\t -> valid <$> tcCallCaseTry γ l fn es ts t) eqLenSigs
  where
    valid (Right (Su m) )   | not (M.null m) 
                            = True
    valid _                 = False
    shd []                  = Nothing
    shd xs                  = Just $ head xs
    isRight (Right _)       = True
    isRight (Left _ )       = False
    eqLenSigs               = mkFun <$> L.filter (eqLen es . snd3) sigs
    sigs                    = catMaybes (bkFun <$> bkAnd ft)

eqLen xs ys       = length xs == length ys 

sameLengthArgs :: [t] -> RType r -> Bool
sameLengthArgs args f = FL.or (bkFun f >>= \(_,bs,_) -> return $ eqLen args bs)
      

tcCallCaseTry γ l fn es' ts ft
  = do let ξ          = tce_ctx γ
       -- Generate fresh type parameters
       (_,ibs,ot)    <- instantiate l ξ fn ft
       let its        = b_type <$> ibs
       θ             <- getSubst 
       defs          <- getTDefs
       --HACK - erase latest annotation on l
       remAnn         $ (srcPos l)
       return         $ unifys (ann l) defs θ ts its

tcCallCase γ l fn es' ts ft 
  = do let ξ          = tce_ctx γ
       -- Generate fresh type parameters
       (_,ibs,ot)    <- instantiate l ξ fn ft
       let its        = b_type <$> ibs
       -- Unify with formal parameter types
       θ             <- unifyTypesM (srcPos l) "tcCall" ts its
       -- Apply substitution
       let (ts',its') = mapPair (apply θ) (ts, its)
       -- Subtype the arguments against the formals and up/down cast if needed 
       es''          <- zipWith3M (castM ξ) es' ts' its'
       return           (es'', apply θ ot)

instantiate l ξ fn ft 
  = do let (αs, t) = bkAll ft
       t'         <- freshTyArgs (srcPos l) ξ αs t 
       maybe err return $ bkFun t'
    where
       err = tcError   $ errorNonFunction (ann l) fn ft


deadCast l γ e 
  = do t'    <- freshTyArgs (srcPos l) ξ [α] t 
       e'    <- addDeadCast ξ e t'
       return   (e', t') 
    where 
      (α, t)  = undefType l γ
      ξ       = tce_ctx γ

undefType l γ 
  = case bkAll $ ut of
      ([α], t) -> (α, t)
      _        -> die $ bug (srcPos l) $ "Malformed type --" ++ ppshow ut ++ "-- for BIUndefined in prelude.js"
    where 
      ut       = builtinOpTy l BIUndefined $ tce_env γ
             
tcPropRead getter γ l e fld = do  
  (e', te)   <- tcExpr γ e
  tdefs      <- getTDefs 
  case getter l (tce_env γ) tdefs fld te of
    Nothing         -> tcError $  errorPropRead (srcPos l) e fld
    Just (te', tf)  -> tcWithThis te $ (, tf) <$> castM (tce_ctx γ) e' te te'

----------------------------------------------------------------------------------
envJoin :: (Ord r, F.Reftable r, PP r) =>
  (AnnSSA r) -> TCEnv r -> TCEnvO r -> TCEnvO r -> TCM r (TCEnvO r)
----------------------------------------------------------------------------------
envJoin _ _ Nothing x           = return x
envJoin _ _ x Nothing           = return x
envJoin l γ (Just γ1) (Just γ2) = envJoin' l γ γ1 γ2 

envJoin' l γ γ1 γ2
  = do let xs = phiVarsAnnot l -- concat [x | PhiVar x <- ann_fact l]
       ts    <- mapM (getPhiType l γ1 γ2) xs
       -- NOTE: Instantiation on arrays could have happened in the branches and
       -- then lost if the variables are no Phi. So replay the application of
       -- the instantiations on γ
       θ     <- getSubst
       return $ Just $ tcEnvAdds (zip xs ts) (apply θ γ)
  

----------------------------------------------------------------------------------
getPhiType ::  (Ord r, F.Reftable r, PP r) => 
  Annot b SourceSpan -> TCEnv r -> TCEnv r -> Id SourceSpan-> TCM r (RType r)
----------------------------------------------------------------------------------
getPhiType l γ1 γ2 x =
  case (tcEnvFindTy x γ1, tcEnvFindTy x γ2) of
    (Just t1, Just t2) -> do  env <- getTDefs
                              return $ fst4 $ compareTs env t1 t2
    (_      , _      ) -> if forceCheck x γ1 && forceCheck x γ2 
                            then tcError $ bug loc "Oh no, the HashMap GREMLIN is back...1"
                            else tcError $ bugUnboundPhiVar loc x
                          where loc = srcPos $ ann l

forceCheck x γ 
  = elem x $ fst <$> envToList (tce_env γ)

