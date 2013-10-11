{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE FlexibleContexts       #-}


module Language.Nano.Typecheck.Typecheck (verifyFile, typeCheck) where 

import           Control.Applicative                ((<$>))
import           Control.Monad                

import qualified Data.HashSet                       as HS 
import qualified Data.HashMap.Strict                as M 
import qualified Data.Traversable                   as T
import qualified Data.List                          as L
import           Data.Monoid
import           Data.Maybe                         (catMaybes, isJust, fromJust)
import           Data.Generics                   
import           Data.Graph
import           Data.Function
import           Data.Tuple

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
import           Language.Nano.Typecheck.Lower
import           Language.Nano.SSA.SSA
import           Language.Nano.Dominators
--import           Language.Nano.HeapTypes.HeapTypes

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
-- verifyFile :: FilePath -> IO (F.FixResult (SourceSpan, String))
--------------------------------------------------------------------------------
--verifyFile f = tc =<< parseNanoFromFile f
--  where 
--   tc pgm    = either unsafe safe . execute pgm . tcNano . ssaTransform $ pgm 

-- | Debug mode
verifyFile f 
   = do nano    <- parseNanoFromFile f
        V.whenLoud $ donePhase FM.Loud "Parse"
        putStrLn . render . pp $ nano
        let nanoSsa = padTransform . ssaTransform $ nano
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
typeCheck ::
  (Data r, Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  V.Verbosity -> Nano (AnnSSA_ r) (RType r) -> Nano (AnnType_ r) (RType r)
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
              Bool -> Nano (AnnSSA_ r) (RType r) -> F.FixResult (SourceSpan, String)
-------------------------------------------------------------------------------
failCasts False (Nano {code = Src fs}) | not $ null csts = F.Unsafe csts
                                       | otherwise       = F.Safe
  where csts = mapFst ann <$> allCasts fs
failCasts True   _                                       = F.Safe                                            
    

-------------------------------------------------------------------------------
allCasts :: (Data r, Typeable r) => [FunctionStatement (AnnSSA_ r)] -> [((AnnSSA_ r), [Char])]
-------------------------------------------------------------------------------
allCasts fs =  everything (++) ([] `mkQ` f) $ fs
  where f (DownCast l t)  = [(l, "DownCast: " ++ ppshow t)]
        f (DeadCast l _)  = [(l, "DeadCode")]
        -- UpCasts are safe
        f _               = [ ]


printAnn (Ann l fs) = when (not $ null fs) $ putStrLn 
    $ printf "At %s: %s" (ppshow l) (ppshow fs)

-------------------------------------------------------------------------------
-- | TypeCheck Nano Program ---------------------------------------------------
-------------------------------------------------------------------------------
-- | The first argument true to tranform casted expressions e to Cast(e,T)
-------------------------------------------------------------------------------
-- tcAndPatch :: (Data r, Typeable r, F.Reftable r, PP r, Ord r) => 
--     Nano (AnnSSA_ r) (RType r) -> TCM r (Nano (AnnSSA_ r) (RType r))
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
checkTypeDefs :: (Data r, Typeable r, F.Reftable r) => Nano (AnnSSA_ r) (RType r) -> TCM r ()
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
tcNano :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  Nano (AnnSSA_ r) (RType r) -> TCM r (Nano (AnnType_ r) (RType r))
-------------------------------------------------------------------------------
tcNano p@(Nano {code = Src fs})
  = do m     <- tcNano' $ {- toType <$> -} p 
       return $ (trace "") $ p {code = Src $ (patchAnn m <$>) <$> fs}
    {-where-}
    {-  cachePP cache = render $-}
    {-        text "********************** CODE **********************"-}
    {-    $+$ pp cache-}
    {-    $+$ text "**************************************************"-}


-------------------------------------------------------------------------------
-- tcNano' :: Nano (AnnSSA_ r) (RType r) -> TCM r AnnInfo  
-------------------------------------------------------------------------------
tcNano' pgm@(Nano {code = Src fs}) 
  = do tcStmts (specs pgm, heapEmpty) fs
       -- tcStmts figured out where some
       -- "meta-statements" need to go (e.g.) renames. 
       -- However, this was figured out ex-post-facto, so
       -- undo these renames 
       as  <- getAllAnns
       as' <- mapM undoRenamesM (zip as $ postDominators pgm)
       return $ M.unions as'

-- patchAnn              :: AnnInfo -> (AnnSSA_ r) -> (AnnType_ r)
patchAnn m (Ann l fs) = Ann l $ {- sortNub $ -} (M.lookupDefault [] l m) ++ fs

-------------------------------------------------------------------------------
-- | (RType r) Check Environment ---------------------------------------------------
-------------------------------------------------------------------------------

--   We define this alias as the "output" type for typechecking any entity
--   that can create or affect binders (e.g. @VarDecl@ or @Statement@)
--   @Nothing@ means if we definitely hit a "return" 
--   @Just γ'@ means environment extended with statement binders

type TCEnv r = Maybe (Env (RType r), RHeap r)

-------------------------------------------------------------------------------
-- | TypeCheck Function -------------------------------------------------------
-------------------------------------------------------------------------------

tcFun (γ,_) (FunctionStmt l f xs body) 
  = do (ft, (αs, ts, σ, σ', t)) <- funTy l f xs
       checkSigWellFormed l ts t σ σ'
       let γ'  = envAdds [(f, ft)] γ
       let γ'' = envAddFun l f αs xs ts t γ'
       accumAnn (\a -> catMaybes (map (validInst γ'') (M.toList a))) $  
         do q              <- withFun (F.symbol f) $ tcStmts (γ'',σ) body
            θ              <- getSubst
            when (isJust q) $ void $ unifyTypeM l "Missing return" f tVoid t
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

checkLocSubs σ =
  do θ <- tracePP "checkLockSubs" <$> getSubst
     when (not $ check θ locs) $ error "Body unifies locations distinct in callee"
  where
    check θ ls = sameLocs $ mapPair L.nub (ls, apply θ ls)
    sameLocs (ls, ls') | length ls == length ls' = all (`elem` ls) ls'
    sameLocs _                                   = False
    locs      = heapLocs σ


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
  = case [β | β <-  HS.toList $ free $ ts, not ((tVarId β) `envMem` γ)] of
      [] -> Nothing
      βs -> Just (l, errorFreeTyVar βs)
   
-- | Strings ahead: HACK Alert
tVarId (TV a l) = Id l $ "TVAR$$" ++ F.symbolString a   

--------------------------------------------------------------------------------
tcSeq :: ((Env (RType r), RHeap r) -> a -> TCM r (TCEnv r)) -> (Env (RType r), RHeap r) -> [a] -> TCM r (TCEnv r)
--------------------------------------------------------------------------------

tcSeq f             = foldM step . Just 
  where 
    step Nothing _  = return Nothing
    step (Just (γ,σ)) x = f (γ,σ) x

--------------------------------------------------------------------------------
tcStmts :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
            (Env (RType r), RHeap r) -> [Statement (AnnSSA_ r)] -> TCM r (TCEnv r)
--------------------------------------------------------------------------------
tcStmts = tcSeq tcStmt

-------------------------------------------------------------------------------
tcStmt  :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
            (Env (RType r), RHeap r) -> Statement (AnnSSA_ r) -> TCM r (TCEnv r)
-------------------------------------------------------------------------------
-- skip
tcStmt' (γ,σ) (EmptyStmt _) 
  = return $ Just (γ,σ)

-- x = e
tcStmt' (γ,σ)  (ExprStmt le (AssignExpr l OpAssign (LVar lx x) e))   
  -- = do uw  <- tc_unwound <$> get
  --      r   <- tcAsgn (γ,σ)  l (Id lx x) e
  = tcAsgn (γ,σ) l (Id lx x) e

-- x.f = e
tcStmt' (γ,σ)  (ExprStmt _ (AssignExpr l OpAssign (LDot ld (VarRef _ x) f) e))   
  = do t <- varLookup γ l x
       tcDotAsgn (γ,σ) l t (Id ld f) e

-- e1.x = e2
-- @e3.x@ should have the exact same type with @e2@
-- tcStmt' (γ,σ) (ExprStmt _ (AssignExpr l2 OpAssign (LDot l3 e3 x) e2))
--   = do  t2 <- tcExpr γ e2 
--         t3 <- tcExpr γ e3
--         tx <- safeDotAccess x t2
--         unifyTypeM l2 "DotRef" e2 t2 tx
--         return $ Just (γ,σ)
-- No strong updates allowed here - so return the same envirnment      

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
tcStmt' (γ,σ) ifstmt@(IfStmt l e s1 s2)
  = do  (t,σe) <- tcExpr (γ,σ) e 
    -- Doing check for boolean for the conditional for now
    -- TODO: Will have to suppert truthy/falsy later.
        unifyTypeM l "If condition" e t tBool
        uw <- getUnwound
        e1 <- preWind uw s1 $ tcStmt (γ, σe) s1
        e2 <- preWind uw s2 $ tcStmt (γ, σe) s2
        envJoin l (γ,σe) e1 e2
    where
      msg s = printf "Unwound in IfStatement %s on statement %s" (ppshow ifstmt) (ppshow s)
      lastStmtAnn (BlockStmt l _) = l
      lastStmtAnn s               = getAnnotation s
      preWind uw s m = do r <- setUnwound uw >> m
                          let l = lastStmtAnn s
                          case r of
                            Just e -> Just <$> windLocations e l 
                            _      -> return r

-- var x1 [ = e1 ]; ... ; var xn [= en];
tcStmt' (γ,σ) (VarDeclStmt _ ds)
  = tcSeq tcVarDecl (γ,σ) ds

-- return e 
tcStmt' (γ,σ) (ReturnStmt l eo) 
  = do  let rt         = envFindReturn γ 
        -- End of basic block --> Wind up locations
        (σ_in, σ_out) <- getFunHeaps γ
        (γ,σ')        <- windLocations (γ,σ) l
        -- May be "free"ing some locations, so lets
        -- get rid of those pesky chaps
        (γ,σ')        <- deleteLocationsM l (γ,σ') σ_in σ_out
        (t,σ')        <- maybe (return (tVoid,σ')) (tcExpr (γ,σ')) eo
        θ_old         <- getSubst
        θ             <- unifyTypeM l "Return" eo t rt
        -- Now unify heap
        θ             <- unifyHeapsM l "Return" (tracePP "unifyHeaps 1" σ') (tracePP "unifyHeaps 2" σ_out)
        -- Apply the substitutions
        let (rt', t')  = mapPair (apply θ) (rt,t)
        σ'            <- safeHeapSubstM σ' 
        -- Record the fact that we may have renamed 
        -- an input location. This is OK if the 
        -- this location does not appear in the 
        -- output spec
        θ             <- recordRenameM (ann l) (partitionRenames θ_old θ σ_in σ_out)
        -- Now we may need to wind up any new locations so that
        -- heap subtyping and unification will go through
        (γ,σ')        <- windSpecLocations (γ, apply θ σ') l σ_out
        -- One last chance to unify any TVars that appeared
        -- in the winding step
        unifyHeapsM l "Return" σ' σ_out
        -- Now safe to check the output heap
        checkLocSubs σ_out
        -- Subtype the arguments against the formals and cast if 
        -- necessary based on the direction of the subtyping outcome
        maybeM_ (\e -> castM e t' rt') eo
        castHeapM γ l (tracePP "sig out" σ') (tracePP "sig out spec" σ_out)
        return Nothing

tcStmt' (γ,σ) s@(FunctionStmt _ _ _ _)
  = tcFun (γ,σ) s
-- OTHER (Not handled)
tcStmt' _ s 
  = convertError "TC Cannot Handle: tcStmt'" s

tcStmt (γ,σ) s 
  = do setStmt $ Just s 
       r <- tcStmt' (γ,σ) s
       setStmt $ Nothing
       return r

getFunHeaps γ
  = do f <- getFun
       case envFindTy f γ of
         Nothing -> error "Unknown current typed function"
         Just z  -> return $ fromJust $ funHeaps z

windLocations (γ,σ) l = getUnwound >>= windLocations' (γ,σ) l

windLocations' (γ,σ) l = foldM (windLocation l) (γ,σ) . tracePP "ordering" .  uwOrder σ . tracePP "pre ordering"

windLocation l (γ,σ) (loc, tWind, _)
  | not $ heapMem loc σ                       = return (γ,σ)
  | isWoundTy (heapRead "windLocation" loc σ) = return (γ,σ)
  | otherwise                  = 
    do let σt       = restrictHeap [loc] $ tracePP ("winding " ++ loc) σ
       let σc       = foldl (flip heapDel) σ $ heapLocs σt
       (_, σe, t')  <- tracePP ("result of windType " ++ loc) <$> windType γ l loc tWind σt
       σr       <- tracePP "sigma r" <$> (safeHeapSubstM $ heapUpd loc t' $ heapCombineWith const [σe, σc])
       uw          <- getUnwound
       setUnwound $ (filter (not.(== loc).fst3)) uw
       return (γ,σr)

windType γ l loc tWind@(Id _ i) σ 
  = do (θα,t')      <- freshApp l tWind
       (σe, t'',θl) <- tracePP (printf "UnwindTC [%s,%s]" (ppshow loc) (ppshow tWind)) <$> unwindTC t'
       let ls        = L.nub $ loc : heapLocs σe ++ locs t''
       let σe_up     = heapAdd "windType" loc t'' σe
       θ            <- tracePP ("Theta of winding " ++ loc) <$> unifyHeapsM l "Wind(heap)" (tracePP "wind prime" σe_up) (tracePP "wind" σ)
       let θ_inst    = θα `mappend` θl
           (σ1, σ2)  = mapPair (apply θ) (σ,σe_up)
           ls'       = apply θ ls
       -- There may be locations (never unwound) that need to get wound up at this point
           σe'       = tracePP "sige'" $ apply θ $ tracePP ("sige loc: " ++ loc) σe
           wls       = tracePP "dependents" $ filter (needWind (tracePP "dependents reference" σ1)) $ tracePP "dependents wound" $ woundLocations $ tracePP ("dependents heap " ++ loc) σ2
       (_,σ1')      <- (\(g,h) -> (g,tracePP "wind recursive result" h)) <$> windLocations' (γ,tracePP "wind recursive" σ1) l wls
       θ' <- unifyHeapsM l "Wind(heap)" σ2 σ1'
       let θf = θ `mappend` θ'
       castHeapM γ l σ1' σ2
       recordWindExpr (ann l) (loc, heapLocs σe', tWind) (θ_inst `mappend` θf)
       return (θf, foldl (flip heapDel) σ1' $ heapLocs σe', apply θf t')
       -- return (θ, tracePP ("windType returning wound up " ++ loc) $ σe',apply θ t')
  where 
    dropThird (a,b,_)  = (a,b)
    needWind σ (l,t,_) = case L.lookup l $ map dropThird $ woundLocations σ of
                           Just t' -> F.symbol t /= F.symbol t'
                           _       -> elem l $ heapLocs σ

uwOrder σ ls = reverse $ map (fst3 . v2e) $ topSort g
  -- For each unwound location l |-> t, record (l, locations referred to by t
  -- build a graph of these dependencies and sort it, then fold locations
  -- in that order
  where deps      = map (\(l,i,θ) ->((l,i,θ),l,locs $ heapRead "uwOrder" l σ)) ls
        (g,v2e,_) = graphFromEdges deps

-- Compare locations in σ with σ_spec using the current θ.
-- If a location exists in both and is wound up in σ_spec,
-- then wind it up here.
windSpecLocations (γ,σ) l σ_spec
  = do θ         <- getSubst
       σ         <- safeHeapSubstM σ
       let wls    = tracePP "windSpecLocations spec" $ woundLocations σ_spec
       let tlocs  = tracePP "windSpecLocations locs" $ heapLocs σ
       let uwls   = tracePP "uwls" [ (l,i,θ) | (l,i,θ) <- wls
                                             , (apply θ l) `elem` tlocs
                                             , not . isWoundTy $ heapRead "windSpecLocations" l σ ]
       windLocations' (γ,σ) l uwls
       -- getUnwound >>= windLocations' (γ,σ) l
       -- withUnwound uwls $ windLocations' (γ,σ) l

isWoundTy (TApp (TDef _) _ _) = True
isWoundTy _                   = False

-------------------------------------------------------------------------------
woundLocations :: (PP r, Ord r, F.Reftable r) => 
                  RHeap r -> [(Location, Id SourceSpan, RSubst r)]
-------------------------------------------------------------------------------
woundLocations σ_spec = [ p | Just p <- map go $ heapBinds σ_spec ]
  where
    go (l, (TApp (TDef d) _ _)) = Just (l, d, mempty)                       
    go _                        = Nothing

-------------------------------------------------------------------------------
tcVarDecl :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  (Env (RType r), RHeap r) -> VarDecl (AnnSSA_ r) -> TCM r (TCEnv r)
-------------------------------------------------------------------------------

tcVarDecl (γ,σ) (VarDecl l x (Just e)) 
  = tcAsgn (γ,σ) l x e  
tcVarDecl γ (VarDecl _ _ Nothing)  
-- TODO: add binding from the declared variable to undefined
  = return $ Just γ

------------------------------------------------------------------------------------
tcAsgn :: (PP r, Ord r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) => 
  (Env (RType r), RHeap r) -> (AnnSSA_ r) -> Id (AnnSSA_ r) -> Expression (AnnSSA_ r) -> TCM r (TCEnv r)
------------------------------------------------------------------------------------

tcAsgn (γ,σ) _ x e 
  = do (t, σ') <- tcExpr (γ,σ) e
       return $ Just (envAdds [(x, t)] γ, σ')

------------------------------------------------------------------------------------
tcDotAsgn :: (PP r, Ord r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  (Env (RType r), RHeap r)
  -> (AnnSSA_ r)
  -> (RType r)
  -> Id (AnnSSA_ r)
  -> Expression (AnnSSA_ r)
  -> TCM r (TCEnv r)
------------------------------------------------------------------------------------
tcDotAsgn (γ,σ) l x f e
  = do (t,σ)            <- tcExpr (γ,σ) e 
       acc              <- safeDotAccess σ f x
       (rs,σ')          <- unpackAccess l σ acc
       let ls            = locs x
       let updFun        = if length ls == 1 then updHeapField else wUpdHeapField
       ts'              <- mapM (updFun σ' t) ls
       let σ_asgn        = heapFromBinds "tcDotAsgn" $ zip ls ts'
       return $ Just (γ, heapCombineWith const [σ_asgn, σ'])
  where  
    updHeapField  σ t loc = return $ updateField t (F.symbol f) (heapRead "updHeapField"  loc σ)
    wUpdHeapField σ t loc =
      do γ  <- getTDefs 
         t' <- updHeapField σ t loc
         return $ fst4 $ compareTs γ (heapRead "wUpdHeapField" loc σ) t'

weakenUpdTy _ t []      = t
weakenUpdTy γ t (t':ts) = 
  weakenUpdTy γ (fst4 $ compareTs γ t t') ts

-------------------------------------------------------------------------------
tcExpr :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  (Env (RType r), RHeap r) -> Expression (AnnSSA_ r) -> TCM r (RType r, RHeap r)
-------------------------------------------------------------------------------
tcExpr (γ,σ) e = setExpr (Just e) >> (tcExpr' (γ,σ) e)


-------------------------------------------------------------------------------
tcExpr' :: (Ord r, PP r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r)) =>
  (Env (RType r), RHeap r) -> Expression (AnnSSA_ r) -> TCM r (RType r, RHeap r)
-------------------------------------------------------------------------------

tcExpr' (_,σ) (IntLit _ _)
  = return (tInt, σ)

tcExpr' (_,σ) (BoolLit _ _)
  = return (tBool, σ)

tcExpr' (_,σ) (StringLit _ _)
  = return (tString, σ)

tcExpr' (_,σ) (NullLit _)
  = return (tNull, σ)

tcExpr' (γ,σ) e@(VarRef l x)
  = do mt <- tcVar (γ,σ) e =<< varLookup γ l x -- >>= tcVar (γ,σ) e
       maybe err return mt
    where
      err = tcError (ann l) (printf "%s out of scope!" (ppshow x))

tcExpr' (γ,σ) (PrefixExpr l o e)
  = tcCall (γ,σ) l o [e] (prefixOpTy o γ)

tcExpr' (γ,σ) (InfixExpr l o e1 e2)        
  = tcCall (γ,σ) l o [e1, e2] (infixOpTy o γ)

tcExpr' (γ,σ) (CallExpr l e es)
  = do (t, σ')  <- tcExpr (γ,σ) e
       tcCall (γ, σ') l e es t

tcExpr' (γ,σ) (ObjectLit l ps) 
  = tcObject (γ,σ) l ps

tcExpr' (γ,σ) (DotRef l e i) 
  = tcAccess (γ,σ) l e i

tcExpr' γ (BracketRef l e (StringLit _ s))
  = tcAccess γ l e s

{--- General case of dynamic key dictionary access-}
{-tcExpr' γ (BracketRef l e1 e2)-}
{-  = do  t2 <- tcExpr γ e2-}
{-        unifyTypeM l "BracketRef" e2 t2 tString-}
{-        tcAccess γ l e1 s-}

tcExpr' _ e 
  = convertError "tcExpr" e
    
tcVar :: (Ord r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r), PP r) => 
  (Env (RType r), RHeap r) -> Expression (AnnSSA_ r) -> RType r -> TCM r (Maybe (RType r, RHeap r))

-- tcVar (γ,σ) e t@(TApp (TRef loc) [] r)   
--   = if loc `elem` heapLocs σ then
--       return $ Just (t,σ)
--     else
--       do castM e t tNull 
--          return $ Just (t,σ)
    
-- tcVar (γ,σ) e t@(TApp TUn ts r)
--   = do ts' <- mapM (tcVar (γ,σ) e) ts 
--        case [ t | Just (t,_) <- ts' ] of
--          []   -> do castM e t tNull 
--                     return $ Just (t,σ)
--          ts'  -> do let t' = mkUnion ts'
--                     castM e t t'
--                     return $ Just (t, σ)
    
tcVar (_,σ) e t = return $ Just (t,σ)                 
        
        

----------------------------------------------------------------------------------
tcCall :: (Ord r, F.Reftable r, Substitutable r (Fact_ r), Free (Fact_ r), PP r, PP fn) => 
  (Env (RType r), RHeap r) -> (AnnSSA_ r) -> fn -> [Expression (AnnSSA_ r)]-> (RType r) -> TCM r (RType r, RHeap r)
----------------------------------------------------------------------------------
tcCall (γ,σ) l fn es ft
  = do  (_,ibs,σi,σo,ot) <- freshFun l fn ft
        let its           = b_type <$> ibs
        -- Typecheck argument
        (ts, σ')         <- foldM (tcExprs γ) ([], σ) es
        -- Unify with formal parameter types
        -- θ <- unifyTypesM l "tcCall" its ts >> unifyHeapsM l "tcCall" σ' σi
        θ <- tracePP "call subst" <$> (unifyTypesM l "tcCall" its ts >> unifyHeapsM l "tcCall" σ' σi)
        -- Apply the substitution
        let (ts',its')    = mapPair (apply θ) (ts,its)
        -- This function call may require some locations
        -- to be folded up. Who are we to argue?
        ls                <- maybe (error "BUG: no statement") getAnnotation <$> getStmt
        (γ,σ')            <- windSpecLocations (γ, (tracePP "tcCall actual heap wind sub" $ apply θ $ tracePP "tcCall actual heap wind" σ')) ls (tracePP "tcCall formal heap wind sub" $ apply θ $ tracePP "tcCall formal heap wind" σi)
        -- Subtype the arguments against the formals and cast if 
        -- necessary based on the direction of the subtyping outcome
        castsM es ts' its' 
        castHeapM γ l (apply θ σ') (apply θ σi)
        checkDisjoint σo
        let σ_out = tracePP "sig out" $ heapCombine "tcCall" [subtr (tracePP "theta call" θ) (tracePP "actual sig in" σ') (tracePP "spec sig in" σi), tracePP "sig out" $ apply θ σo]
        return (apply θ ot, apply θ σ_out)
    where
      subtr θ σ1 σ2   = foldl (flip heapDel) σ1 $ apply θ $ heapLocs σ2
      checkDisjoint σ = do σ' <- safeHeapSubstWithM (\_ _ _ -> Left ()) σ
                           case [m | (m, Left _) <- heapBinds σ'] of
                             [] -> return ()
                             _  -> tcError (ann l) "Call joins locations that are distinct in callee"

tcExprs γ (ts,σ) e = do (t,σ') <- tcExpr (γ,σ) e
                        return (ts ++ [t], σ')

----------------------------------------------------------------------------------
tcObject ::  (Ord r, F.Reftable r, PP r, Substitutable r (Fact_ r), Free (Fact_ r)) => 
  (Env (RType r), RHeap r) -> AnnSSA_ r -> [(Prop (AnnSSA_ r), Expression (AnnSSA_ r))] -> TCM r (RType r, RHeap r)
----------------------------------------------------------------------------------
tcObject (γ,σ) l bs 
  = do loc          <- freshLocation l
       let (ps, es)  = unzip bs
       (ts,σ')      <- foldM (tcExprs γ) ([],σ) es
       let bts       =  zipWith B (map F.symbol ps) ts
       let t         = TObj bts F.top 
       return (tRef loc, heapAdd "tcObject" loc t σ')

----------------------------------------------------------------------------------
tcAccess ::  (Ord r, F.Reftable r, PP r, F.Symbolic s,
              Substitutable r (Fact_ r), Free (Fact_ r), PP s) =>
  (Env (RType r), RHeap r) -> (AnnSSA_ r) -> Expression (AnnSSA_ r) -> s -> TCM r (RType r, RHeap r)
----------------------------------------------------------------------------------
tcAccess (γ,σ) l e f = 
  do (r,σ') <- tcExpr (γ,σ) e
     tcAccess' l σ' r f

tcAccess' l σ t f = safeDotAccess ((tracePP "safeDotAccess" (σ,f,t))`seq`σ) f t >>= unpackAccess l σ

-- After accessing a field on the heap, unpack the results and:
--   1. Return the result of the access
--   2. Update unfolded locations AND add new locations
-------------------------------------------------------------------------------
unpackAccess :: (Ord r, PP r, F.Reftable r) => 
  AnnSSA_ r -> (RHeap r) -> [(Location, ObjectAccess r)] -> TCM r (RType r, RHeap r)
-------------------------------------------------------------------------------
unpackAccess l σ acc
  = do when (not $ ckDisjoint ls ls') $
         error "BUG: Access resulted in non-disjoint new heap!"
       when (not $ ckSameUnfolds ufs) $
         error "BUG: Access resulted in two different unfoldings!"
       return env
  where
    env             = (mkUnion rs, heapCombineWith const [σ_unfold,σ_new,σ])
    (ls, ls')       = mapPair heapLocs (σ, σ_new)
    σ_new           = tracePP "unpackAccess new" $ heapCombine   "unpackAccess new" $ catMaybes hs 
    σ_unfold        = tracePP "unpackAccess unfold" $ heapFromBinds "unpackAccess unfold" $ [ (l,t) | (l, Just t) <-  ufs ]
    (rs, hs, ufs)   = unzip3 $ unpk <$> acc
    -- unwinds         = [(l,i) | (l, Just i) <- map (fmap (fmap fst3 . ac_unfold)) acc ]
    unpk (l,a)      = (ac_result a, ac_heap a, (l, thd3 <$> ac_unfold a))
    
ckDisjoint l l' = 
  L.intersect l l' == []

ckSameUnfolds ufs     
  = all check ufss
    where ufss  = L.groupBy ((==)`on`fst) ufs
          check []     = True
          check (t:ts) = all (== t)  ts

----------------------------------------------------------------------------------
envJoin :: (Ord r, F.Reftable r, PP r) =>
  (AnnSSA_ r) -> (Env (RType r), RHeap r) -> TCEnv r -> TCEnv r -> TCM r (TCEnv r)
----------------------------------------------------------------------------------
envJoin _ _ Nothing x           = return x
envJoin _ _ x Nothing           = return x
envJoin l (γ,σ) (Just (γ1,σ1)) (Just (γ2,σ2)) = envJoin' l (γ,tracePP "join under" σ) (γ1,tracePP "joining 1" σ1) (γ2, tracePP "joining 2" σ2) 

envJoin' l (γ,_) (γ1,σ1) (γ2,σ2)
  = do let xs = [x | PhiVar x <- ann_fact l]
       ts    <- mapM (getPhiType l (γ1,σ1) (γ2,σ2)) xs
       env   <- getTDefs
       return $ Just $ (envAdds (zip xs ts) γ, heapCombineWith (combine env) [σ1,σ2])
       where
         combine e t1 t2 = fst4 $ compareTs e t1 t2
  

----------------------------------------------------------------------------------
getPhiType ::  (Ord r, F.Reftable r, PP r) => 
  Annot b SourceSpan -> (Env (RType r), RHeap r) -> (Env (RType r), RHeap r) -> Id SourceSpan-> TCM r (RType r)
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

----------------------------------------------------------------------------------
deleteLocationsM :: (Ord r, F.Reftable r, PP r) =>
  Annot b SourceSpan -> (Env (RType r), RHeap r) -> RHeap r -> RHeap r -> TCM r (Env (RType r), RHeap r)
----------------------------------------------------------------------------------
deleteLocationsM l (γ,σ) σi σo
  = do θ <- getSubst
       setSubst . uncurry fromLists . fmap (filter ((`notElem` del) . fst)) $ toLists θ
       -- Locations...begone!
       recordDeleteM (ann l) del
       return $ (envMap (deleteLocsTy del) γ, restrictHeap keep $ (deleteLocsTy del) <$> σ)
    where 
      (del, keep) = L.partition deadLoc $ heapLocs σ
      deadLoc l   = l `elem` heapLocs σi && l `notElem` heapLocs σo
      

forceCheck x (γ,_) 
  = elem x $ fst <$> envToList γ

varLookup γ l x
  = case envFindTy x γ of 
      Nothing -> logError (ann l) (errorUnboundIdEnv x γ) tErr
      Just z  -> return z
    
partitionRenames :: (F.Reftable r, PP r, Ord r) =>    
  RSubst r -> RSubst r -> RHeap r -> RHeap r -> (RSubst r, RSubst r, RSubst r)
partitionRenames θ_old θ σ1 σ2 = (θ', θr, θrInv)
    where 
      θ'             = foldl (revertSub θ_old renameLocs) θ $ map fst lsubs
      renameLocs     = M.keys . locSub $ θrInv
      (_, lsubs) = toLists θ
      -- 
      (θr,θrInv)     = (fromLists [] sub, fromLists [] (map swap sub))
      sub            = filter rename $ snd $ toLists θ
      (l1s,l2s)      = mapPair heapLocs (σ1,σ2)
      rename (_,l2) = l2 `elem` l2s && l2 `notElem` l1s


revertSub :: (F.Reftable r, PP r, Ord r) => RSubst r -> [Location] -> RSubst r -> Location -> RSubst r
revertSub θ_old renames θ l = 
  if l `notElem` renames && l' `elem` renames then 
    doRevert undo vs ls
  else
    θ
  where
    l'      = apply θ l 
    (vs,ls) = toLists θ
    undo    = fromLists [] [(l', apply θ_old l)]

doRevert :: (F.Reftable r, PP r, Ord r) => RSubst r -> [(TVar, RType r)] -> [(Location, Location)] -> RSubst r
doRevert θ vs ls       
  = fromLists (map (apply θ <$>) vs) (map (apply θ <$>) ls)
