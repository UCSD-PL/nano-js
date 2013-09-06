{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TupleSections          #-}


module Language.Nano.Typecheck.Typecheck (verifyFile, typeCheck) where 

import           Control.Applicative                ((<$>))
import           Control.Monad                

import qualified Data.HashSet                       as HS 
import qualified Data.HashMap.Strict                as M 
import qualified Data.Traversable                   as T
import qualified Data.List                      as L
import           Data.Monoid
import           Data.Maybe                         (catMaybes, isJust, fromJust)
import           Data.Generics                   

import           Text.PrettyPrint.HughesPJ          (text, render, vcat, ($+$), (<+>))
import           Text.Printf                        (printf)

import           Language.Nano.CmdLine              (getOpts)
import           Language.Nano.Errors
import           Language.Nano.Types
import           Language.Nano.Env
import           Language.Nano.Misc
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Parse 
import           Language.Nano.Typecheck.TCMonad
import           Language.Nano.Typecheck.Subst
import           Language.Nano.SSA.SSA

import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc             as FM 
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser        (SourceSpan (..))
import           Debug.Trace                        hiding (traceShow)

import qualified System.Console.CmdArgs.Verbosity as V


--------------------------------------------------------------------------------
-- | Top-level Verifier 
--------------------------------------------------------------------------------
verifyFile :: FilePath -> IO (F.FixResult (SourceSpan, String))
--------------------------------------------------------------------------------
--verifyFile f = tc =<< parseNanoFromFile f
--  where 
--   tc pgm    = either unsafe safe . execute pgm . tcNano . ssaTransform $ pgm 

-- | Debug mode
verifyFile f 
   = do nano    <- parseNanoFromFile f
        V.whenLoud $ donePhase FM.Loud "Parse"
        {-putStrLn . render . pp $ nano-}
        let nanoSsa = ssaTransform nano
        V.whenLoud $ donePhase FM.Loud "SSA Transform"
        V.whenLoud $ putStrLn . render . pp $ nanoSsa
        verb    <- V.getVerbosity
        let p =  execute verb nanoSsa $ tcAndPatch nanoSsa
        TC{ noFailCasts = nfc } <- getOpts
        r <- either unsafe (\q -> safe q >>= return . (`mappend` failCasts nfc q)) p
        V.whenLoud $ donePhase FM.Loud "Typechecking"
        return $ r


-- TODO: CHECK HEAP WF
-------------------------------------------------------------------------------
typeCheck     :: (Data r, Typeable r, F.Reftable r) => V.Verbosity -> 
                   Nano AnnSSA (RType r) -> (Nano AnnType (RType r))
-------------------------------------------------------------------------------
typeCheck verb pgm = either crash id (execute verb pgm (tcAndPatch pgm))
  where
    crash          = errorstar . render . vcat . map (text . ppErr)


unsafe errs = do putStrLn "\n\n\nErrors Found!\n\n" 
                 forM_ errs (putStrLn . ppErr) 
                 return $ F.Unsafe errs

ppErr (l, e) = printf "Error at %s\n  %s\n" (ppshow l) e

safe (Nano {code = Src fs})
  = do V.whenLoud $ forM_ fs $ T.mapM printAnn
       return F.Safe 

-------------------------------------------------------------------------------
failCasts :: (Data r, Typeable r) => 
  Bool -> Nano AnnSSA (RType r) -> F.FixResult (SourceSpan, String)
-------------------------------------------------------------------------------
failCasts False (Nano {code = Src fs}) | not $ null csts = F.Unsafe csts
                                       | otherwise       = F.Safe
  where csts = mapFst ann <$> allCasts fs
failCasts True   _                                       = F.Safe                                            
    

-------------------------------------------------------------------------------
allCasts :: [FunctionStatement AnnSSA] -> [(AnnSSA, [Char])]
-------------------------------------------------------------------------------
allCasts fs =  everything (++) ([] `mkQ` f) $ fs
  where f (DownCast l t)  = [(l, "DownCast: " ++ ppshow t)]
        f (DeadCast l _)  = [(l, "DeadCode")]
        -- UpCasts are safe
        f _               = [ ]


-------------------------------------------------------------------------------
printAnn :: AnnBare -> IO () 
-------------------------------------------------------------------------------
printAnn (Ann l fs) = when (not $ null fs) $ putStrLn 
    $ printf "At %s: %s" (ppshow l) (ppshow fs)

-------------------------------------------------------------------------------
-- | TypeCheck Nano Program ---------------------------------------------------
-------------------------------------------------------------------------------
-- | The first argument true to tranform casted expressions e to Cast(e,T)
-------------------------------------------------------------------------------
tcAndPatch :: (Data r, Typeable r, F.Reftable r) => 
    Nano AnnSSA (RType r) -> TCM (Nano  AnnSSA (RType r))
-------------------------------------------------------------------------------
tcAndPatch p = 
  do  checkTypeDefs p
      p1 <- tcNano p 
      p2 <- patchPgmM p1
      s  <- getSubst
      c  <- getCasts
      hc <- getHCasts
      whenQuiet' (return p2) (return $ trace (codePP p2 s c hc) p2)
      -- return p1
  where 
    codePP (Nano {code = Src src}) sub cst hcst = render $
          text "********************** CODE **********************"
      $+$ pp src
      $+$ text "***************** SUBSTITUTIONS ******************"
      $+$ pp sub
      $+$ text "******************** CASTS ***********************"
      $+$ vcat ((\(e,t) -> (pp $ ann $ getAnnotation e) <+> pp (e,t)) <$> cst)
      $+$ text "****************** HEAP CASTS ********************"
      $+$ vcat ((\(e,t) -> (pp $ ann $ getAnnotation e) <+> pp (e,t)) <$> hcst)
      $+$ text "**************************************************"



-------------------------------------------------------------------------------
checkTypeDefs :: (Data r, Typeable r, F.Reftable r) => Nano AnnSSA (RType r) -> TCM ()
-------------------------------------------------------------------------------
checkTypeDefs pgm = reportAll $ grep
  where 
    ds        = defs pgm 
    ts        = tDefs pgm
    reportAll = mapM_ report
    report t  = tcError (srcPos t) $ errorUnboundType (ppshow t)

    -- There should be no undefined type constructors
    grep :: [Id SourceSpan] = everything (++) ([] `mkQ` g) ds
    g (TDef i) | not $ envMem i ts = [i]
    g _                            = [ ]
  
    -- TODO: Also add check for free top-level type variables, i.e. make sure 
    -- all type variables used are bound. Use something like:
    -- @everythingWithContext@


-------------------------------------------------------------------------------
tcNano :: (F.Reftable r) => Nano AnnSSA (RType r) -> TCM (Nano AnnType (RType r)) 
-------------------------------------------------------------------------------
tcNano p@(Nano {code = Src fs})
  = do m     <- tcNano' $ toType <$> p 
       return $ (trace "") $ p {code = Src $ (patchAnn m <$>) <$> fs}
    {-where-}
    {-  cachePP cache = render $-}
    {-        text "********************** CODE **********************"-}
    {-    $+$ pp cache-}
    {-    $+$ text "**************************************************"-}


-------------------------------------------------------------------------------
tcNano' :: Nano AnnSSA Type -> TCM AnnInfo  
-------------------------------------------------------------------------------
tcNano' pgm@(Nano {code = Src fs}) 
  = do tcStmts (specs pgm, heapEmpty) fs
       M.unions <$> getAllAnns

patchAnn              :: AnnInfo -> AnnSSA -> AnnType
patchAnn m (Ann l fs) = Ann l $ sortNub $ (M.lookupDefault [] l m) ++ fs

-------------------------------------------------------------------------------
-- | Type Check Environment ---------------------------------------------------
-------------------------------------------------------------------------------

--   We define this alias as the "output" type for typechecking any entity
--   that can create or affect binders (e.g. @VarDecl@ or @Statement@)
--   @Nothing@ means if we definitely hit a "return" 
--   @Just γ'@ means environment extended with statement binders

type TCEnv = Maybe (Env Type, BHeap)

-------------------------------------------------------------------------------
-- | TypeCheck Function -------------------------------------------------------
-------------------------------------------------------------------------------

tcFun    :: (Env Type, BHeap) -> FunctionStatement AnnSSA -> TCM TCEnv 
tcFun (γ,_) (FunctionStmt l f xs body) 
  = do (ft, (αs, ts, σ, σ', t)) <- funTy l f xs
       checkSigWellFormed l ts t σ σ'
       let γ'  = envAdds [(f, ft)] γ
       let γ'' = envAddFun l f αs xs ts t γ'
       setFun (F.symbol f)
       accumAnn (\a -> catMaybes (map (validInst γ'') (M.toList a))) $  
         do q              <- tcStmts (γ'',σ) body
            θ              <- getSubst
            checkLocSubs θ σ'
            when (isJust q) $ void $ unifyTypeM l "Missing return" heapEmpty f tVoid t
       return $ Just (γ', heapEmpty)

    
tcFun _  _ = error "Calling tcFun not on FunctionStatement"

checkSigWellFormed l ts t σ σ'
  = do when (not . all (`heapMem` σ) $ concatMap locs ts) $
         tcError (ann l) (printf "Arguments refer to locations not in %s" (ppshow σ))
       when (not . all (`heapMem` σ') $ locs t) $
         tcError (ann l) (printf "Return type refers to locations not in %s" (ppshow σ))
       checkHeapClosed l σ
       checkHeapClosed l σ'

checkHeapClosed l σ =
  if all (flip elem ls) ls' then
    return ()
  else
    tcError (ann l) (printf "Heap %s is not well formed" (ppshow σ))
  where
    ls       = L.nub $ heapLocs σ
    ls'      = L.nub $ concatMap locs $ heapTypes σ

checkLocSubs θ σ =
    if check locs then
        return ()
    else
        error "unifies thingers"
  where
    check ls = sameLocs $ mapPair L.nub (ls, apply θ ls)
    sameLocs (ls, ls') | length ls == length ls' = all (`elem` ls) ls'
    sameLocs (ls, ls') | otherwise               = False
    locs = heapLocs σ


funTy l f xs 
  = do ft <- getDefType f 
       case bkFun ft of
         Nothing        -> logError (ann l) (errorUnboundId f) (tErr, tFunErr)
         Just (αs,ts,σ,σ',t) -> do when (length xs /= length ts) $ logError (ann l) errorArgMismatch ()
                                   return (ft, (αs, b_type <$> ts, σ, σ', t))

envAddFun _ f αs xs ts t = envAdds tyBinds . envAdds (varBinds xs ts) . envAddReturn f t 
  where  
    tyBinds              = [(tVarId α, tVar α) | α <- αs]
    varBinds             = zip
    
    -- tyBinds              = [(Loc (srcPos l) α, tVar α) | α <- αs]

validInst γ (l, ts)
  = case [β | β <-  HS.toList $ free ts, not ((tVarId β) `envMem` γ)] of
      [] -> Nothing
      βs -> Just (l, errorFreeTyVar βs)
   
-- | Strings ahead: HACK Alert
tVarId (TV a l) = Id l $ "TVAR$$" ++ F.symbolString a   

--------------------------------------------------------------------------------
tcSeq :: ((Env Type, BHeap) -> a -> TCM TCEnv) -> (Env Type, BHeap) -> [a] -> TCM TCEnv
--------------------------------------------------------------------------------

tcSeq f             = foldM step . Just 
  where 
    step Nothing _  = return Nothing
    step (Just (γ,σ)) x = f (γ,σ) x

--------------------------------------------------------------------------------
tcStmts :: (Env Type, BHeap) -> [Statement AnnSSA] -> TCM TCEnv
--------------------------------------------------------------------------------
tcStmts = tcSeq tcStmt

-------------------------------------------------------------------------------
tcStmt :: (Env Type, BHeap) -> Statement AnnSSA -> TCM TCEnv  
-------------------------------------------------------------------------------
-- skip
tcStmt' (γ,σ) (EmptyStmt _) 
  = return $ Just (γ,σ)

-- x = e
tcStmt' (γ,σ)  (ExprStmt _ (AssignExpr l OpAssign (LVar lx x) e))   
  = tcAsgn (γ,σ)  l (Id lx x) e

-- x.f = e
tcStmt' (γ,σ)  (ExprStmt _ (AssignExpr l OpAssign (LDot ld (VarRef lx x) f) e))   
  = tcDotAsgn (γ,σ) l x e (Id ld f)

-- e
tcStmt' (γ,σ) (ExprStmt _ e)   
  = tcExpr (γ,σ) e >>= \(_,σ') -> return $ Just (γ,σ')

-- s1;s2;...;sn
tcStmt' (γ,σ) (BlockStmt _ stmts) 
  = tcStmts (γ,σ) stmts 

-- if b { s1 }
tcStmt' (γ,σ) (IfSingleStmt l b s)
  = tcStmt' (γ,σ) (IfStmt l b s (EmptyStmt l))

-- if b { s1 } else { s2 }
tcStmt' (γ,σ) (IfStmt l e s1 s2)
  = do  (t,σe) <- tcExpr (γ,σ) e 
    -- Doing check for boolean for the conditional for now
    -- TODO: Will have to suppert truthy/falsy later.
        (_,σ') <- unifyTypeM l "If condition" σe e t tBool
        e1     <- tcStmt' (γ, σ') s1
        e2     <- tcStmt' (γ, σ') s2
        envJoin l (γ,σ') e1 e2

-- var x1 [ = e1 ]; ... ; var xn [= en];
tcStmt' (γ,σ) (VarDeclStmt _ ds)
  = tcSeq tcVarDecl (γ,σ) ds

-- return e 
tcStmt' (γ,σ) (ReturnStmt l eo) 
  = do  (t,σ')            <- maybe (return (tVoid,heapEmpty)) (tcExpr (γ,σ)) eo
        let rt             = envFindReturn γ 
        (_, σ_out)        <- getFunHeaps γ
        (θ',σ'')          <- unifyTypeM l "Return" σ' eo t rt
        (θ',σ'')          <- unifyHeapsM l "Return" σ'' σ_out
        -- Apply the substitution
        let (rt', t')       = mapPair (apply θ') (rt,t)
        -- Subtype the arguments against the formals and cast if 
        -- necessary based on the direction of the subtyping outcome
        maybeM_ (\e -> castM e t' rt') eo
        maybeM_ (\e -> castHeapM γ e  σ'' σ_out) eo
        return Nothing

tcStmt' (γ,σ) s@(FunctionStmt _ _ _ _)
  = tcFun (γ,σ) s

-- OTHER (Not handled)
tcStmt' _ s 
  = convertError "TC Cannot Handle: tcStmt'" s

tcStmt (γ,σ) s = tcStmt' (γ,σ) s

getFunHeaps γ
  = do Just f             <- getFun
       (_,_,σ_in,σ_out,_) <- case envFindTy f γ of 
                            Nothing -> error "Unknown current typed function"
                            Just z  -> return $ fromJust $ bkFun z 
       return (σ_in, σ_out)

-------------------------------------------------------------------------------
tcVarDecl :: (Env Type, BHeap) -> VarDecl AnnSSA -> TCM TCEnv  
-------------------------------------------------------------------------------

tcVarDecl (γ,σ) (VarDecl l x (Just e)) 
  = tcAsgn (γ,σ) l x e  
tcVarDecl γ (VarDecl _ _ Nothing)  
-- TODO: add binding from the declared variable to undefined
  = return $ Just γ

------------------------------------------------------------------------------------
tcAsgn :: (Env Type, BHeap) -> AnnSSA -> Id AnnSSA -> Expression AnnSSA -> TCM TCEnv
------------------------------------------------------------------------------------

tcAsgn (γ,σ) _ x e 
  = do (t, σ') <- tcExpr (γ,σ) e
       return $ Just (envAdds [(x, t)] γ, σ')

------------------------------------------------------------------------------------
tcDotAsgn :: (Env Type, BHeap)
          -> AnnSSA
          -> Id AnnSSA
          -> Expression AnnSSA
          -> Id AnnSSA
          -> TCM TCEnv
------------------------------------------------------------------------------------
tcDotAsgn (γ,σ) l x e f
  = do t      <- varLookup γ l x
       let lx  = location t
       let t   = heapRead lx σ
       return $ Just (γ,σ)



-------------------------------------------------------------------------------
tcExpr :: (Env Type, BHeap) -> Expression AnnSSA -> TCM (Type, BHeap)
-------------------------------------------------------------------------------
tcExpr (γ,σ) e = setExpr (Just e) >> (tcExpr' (γ,σ) e)


-------------------------------------------------------------------------------
tcExpr' :: (Env Type, BHeap) -> Expression AnnSSA -> TCM (Type, BHeap)
-------------------------------------------------------------------------------

tcExpr' (_,σ) (IntLit _ _)
  = return (tInt, σ)

tcExpr' (_,σ) (BoolLit _ _)
  = return (tBool, σ)

tcExpr' (_,σ) (StringLit _ _)
  = return (tString, σ)

tcExpr' (_,σ) (NullLit _)
  = return (tNull, σ)

tcExpr' (γ,σ) (VarRef l x)
  = varLookup γ l x >>= return . (,σ)

tcExpr' (γ,σ) (PrefixExpr l o e)
  = tcCall (γ,σ) l o [e] (prefixOpTy o γ)

tcExpr' (γ,σ) (InfixExpr l o e1 e2)        
  = tcCall (γ,σ) l o [e1, e2] (infixOpTy o γ)

-- TODO: HACK
tcExpr' (γ,σ) x@(CallExpr l (VarRef _ (Id _ "wind")) es)
  = tcWind (γ,σ) l es

-- TODO: HACK
tcExpr' (γ,σ) (CallExpr l (VarRef _ (Id _ "unwind")) es)
  = tcUnwind (γ,σ) l es

tcExpr' (γ,σ) (CallExpr l e es)
  = do (t, σ')  <- tcExpr (γ,σ) e
       tcCall (γ, σ') l e es t

tcExpr' (γ,σ) (ObjectLit _ ps) 
  = tcObject (γ,σ) ps

tcExpr' (γ,σ) (DotRef l e i) 
  = tcAccess (γ, σ) l e i

tcExpr' _ e 
  = convertError "tcExpr" e

----------------------------------------------------------------------------------
tcCall :: (PP fn) => (Env Type, BHeap) -> AnnSSA -> fn -> [Expression AnnSSA]-> Type -> TCM (Type, BHeap)
----------------------------------------------------------------------------------
tcCall (γ,σ) l fn es ft
  = do  (_,ibs,σi,σo,ot) <- instantiate l fn ft
        let its           = b_type <$> ibs
        -- Typecheck arguments
        (ts, σ')         <- foldM (tcExprs γ) ([], σ) es
        -- Unify with formal parameter types
        (θ,σ'')          <- unifyTypesM l "tcCall" σ' its ts
        (θ,σ'')          <- unifyHeapsM l "tcCall" σ'' σi
        -- Apply the substitution
        let (ts',its') = mapPair (apply θ) (ts,its)
        -- Subtype the arguments against the formals and cast if 
        -- necessary based on the direction of the subtyping outcome
        castsM es ts' its'
        eh <- tick >>= return . VarRef l . Id l . show
        castHeapM γ eh σ'' σi
        checkDisjoint σo
        let σ_out         = heapCombineWith (curry snd) [σ'', (apply θ σo)]
        return $ (apply θ ot, σ_out)
    where
      checkDisjoint σ = do σ' <- safeHeapSubstWithM (\_ _ _ -> Left ()) σ
                           case [m | (m, Left _) <- heapBinds σ'] of
                             [] -> return ()
                             _  -> tcError (ann l) "Call joins locations that are distinct in callee"

tcExprs γ (ts,σ) e = do (t,σ') <- tcExpr (γ,σ) e
                        return (ts ++ [t], σ')

instantiate l fn ft 
  = do t' <-  {- tracePP "new Ty Args" <$> -} freshTyArgs (srcPos l) (bkAll ft)
       (ts,ibs,σi,σo,ot) <- maybe err return $ bkFun t'
       (θi,_,σi')        <- freshHeap σi
       (θo,_,σo')        <- freshHeap (apply θi σo)
       let θ              = θi `mappend` θo
       return $ (ts, map (apply θ) ibs, apply θo σi', σo', apply θ ot)
    where
       err = logError (ann l) (errorNonFunction fn ft) tFunErr



----------------------------------------------------------------------------------
tcObject :: (Env Type, BHeap) -> [(Prop AnnSSA, Expression AnnSSA)] -> TCM (Type, BHeap)
----------------------------------------------------------------------------------
tcObject (γ,σ) bs 
  = do 
      l <- freshLocation
      let (ps, es) = unzip bs
      (ts,σ') <- foldM (tcExprs γ) ([],σ) es
      let bts =  zipWith B (map F.symbol ps) ts
      let t   = TObj bts ()
      return (tRef l, heapAdd l t σ')

----------------------------------------------------------------------------------
tcUnwind :: (Env Type, BHeap) -> AnnSSA -> [Expression AnnSSA] -> TCM (Type, BHeap)
----------------------------------------------------------------------------------
tcUnwind (γ,σ) a [e]
  = do loc         <- freshLocation
       (t,σ')      <- tcExpr (γ,σ) e
       (θ,σ'')     <- unifyTypeM a "Unwind" σ' e t (tRef loc)
       let l'       = apply θ $ location t
       (σt,tc)     <- unwindTC $ heapRead l' σ''
       (θ',_,σt')  <- freshHeap σt
       return (tVoid, heapCombine [heapUpd l' (apply θ' tc) σ'', σt'])
tcUnwind _ l _
  = tcError (ann l) "Unwind called with wrong number of arguments"

----------------------------------------------------------------------------------
tcWind :: (Env Type, BHeap) -> AnnSSA -> [Expression AnnSSA] -> TCM (Type, BHeap)
----------------------------------------------------------------------------------
tcWind (γ,σ) a (e:es)
  = do loc             <- freshLocation
       (t,σ')          <- tcExpr (γ,σ) e
       (θ,σ'')         <- unifyTypeM a "Wind" σ' e t (tRef loc)
       let l'           = apply θ $ location t
       let th           = heapRead l' σ''
       let ls           = locs th
       let σt           = restrictHeap ls σ''
       let σc           = foldl (flip heapDel) σ'' $ heapLocs σt
       (θt, σt', t')   <- windType γ a e (apply θ th) σt es
       return $ (tVoid, heapUpd l' t' σc)
tcWind _ l _ 
  = tcError (ann l) "Wind called with wrong number of arguments"
    
-- TODO: TVars
windType γ l e t σ ((VarRef _ i@(Id l' x)):es)
  = do t'         <- freshApp l i
       (σe, t'')  <- unwindTC t'
       (θ,σ')     <- unifyTypeM l "Wind" σ e t t''
       (θ,σ')     <- tracePP "thinger" <$> unifyHeapsM l "Wind" σ' σe
       castM e (apply θ t) (apply θ t'')
       castHeapM γ e (apply θ σ') (apply θ σe)
       return (θ,σ',t')

freshApp l (Id l' x)
  = do γ <- getTDefs
       case envFindTy x γ of
         Just (TBd (TD _ vs _ _ _ )) -> 
           do θ <- freshSubst (ann l) vs
              let ts = apply θ . tVar <$> vs
              return $ TApp (TDef (Id (ann l') x)) ts ()
         _                           ->
           error$ errorUnboundId x

----------------------------------------------------------------------------------
tcAccess :: (Env Type, BHeap) -> AnnSSA -> Expression AnnSSA -> Id AnnSSA -> TCM (Type, BHeap)
----------------------------------------------------------------------------------
tcAccess (γ,σ) _ e f = 
  do (r,σ') <- tcExpr (γ,σ) e
     tcAccess' σ' r f

tcAccess' σ (TApp TNull [] _) f = return $ (tUndef, σ)
tcAccess' σ t f = do acc       <- dotAccessRef σ f t
                     let (tr,newBinds,σt)  = fromJust acc
                     let σ' = heapCombineWith (curry snd) [σ, heapFromBinds newBinds]
                     return $ (tr, heapCombine [σ',σt])

location (TApp (TRef l) [] _) = l
location t                    = error $ "location of non-ref " ++ (ppshow t)
                              
----------------------------------------------------------------------------------
envJoin :: AnnSSA -> (Env Type, BHeap) -> TCEnv -> TCEnv -> TCM TCEnv 
----------------------------------------------------------------------------------
envJoin _ _ Nothing x           = return x
envJoin _ _ x Nothing           = return x
envJoin l (γ,σ) (Just (γ1,σ1)) (Just (γ2,σ2)) = envJoin' l (γ,σ) (γ1,σ1) (γ2,σ2) 

envJoin' l (γ,_) (γ1,σ1) (γ2,σ2)
  = do let xs = [x | PhiVar x <- ann_fact l]
       ts    <- mapM (getPhiType l (γ1,σ1) (γ2,σ2)) xs
       env   <- getTDefs
       return $ Just $ (envAdds (zip xs ts) γ, heapCombineWith (combine env) [σ1,σ2])
       where
        combine e = (fst4.) . (compareTs e)
  

----------------------------------------------------------------------------------
getPhiType :: Annot b SourceSpan -> (Env Type, BHeap) -> (Env Type, BHeap) -> Id SourceSpan-> TCM Type
----------------------------------------------------------------------------------
getPhiType l (γ1,σ1) (γ2,σ2) x =
  case (envFindTy x γ1, envFindTy x γ2) of
    (Just t1, Just t2) -> do  env <- getTDefs
                              return $ fst4 $ compareTs env t1 t2
                          {-if t1 == t2-}
                          {-  then return t1 -}
                          {-  else tcError l $ errorJoin x t1 t2-}
    (_      , _      ) -> if forceCheck x (γ1,σ1) && forceCheck x (γ2,σ2) 
                            then tcError (ann l) "Oh no, the HashMap GREMLIN is back...1"
                            else tcError (ann l) (bugUnboundPhiVar x)



forceCheck x (γ,_) 
  = elem x $ fst <$> envToList γ

varLookup γ l x
  = case envFindTy x γ of 
      Nothing -> logError (ann l) (errorUnboundIdEnv x γ) tErr
      Just z  -> return z
