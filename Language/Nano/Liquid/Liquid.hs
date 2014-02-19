{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}

-- | Top Level for Refinement Type checker

module Language.Nano.Liquid.Liquid (verifyFile) where

import           Text.Printf                        (printf)
import           Control.Monad
import           Control.Applicative                ((<$>))

import qualified Data.ByteString.Lazy               as B
import qualified Data.HashMap.Strict                as M
import           Data.Maybe                         (fromJust)
import           Data.Monoid
import           Data.List                          (nub, union)

import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Syntax.Annotations
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Parser        (SourceSpan (..))

import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Files
import           Language.Fixpoint.Interface        (solve)

import           Language.Nano.CmdLine              (getOpts)
import           Language.Nano.Errors
import           Language.Nano.Env                  (envUnion, envMap)
import           Language.Nano.Types
import qualified Language.Nano.Annots               as A
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.Lower
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Typecheck  (typeCheck) 
import           Language.Nano.Typecheck.Compare
import           Language.Nano.Typecheck.Parse
import           Language.Nano.SSA.SSA
import           Language.Nano.Liquid.Types
import           Language.Nano.Liquid.CGMonad
import           Language.Nano.Liquid.Measures
import           Language.Nano.Liquid.Predicates
import           Language.Nano.Misc

import           System.Console.CmdArgs.Default

import qualified System.Console.CmdArgs.Verbosity as V

--------------------------------------------------------------------------------
verifyFile       :: FilePath -> IO (F.FixResult (SourceSpan, String))
--------------------------------------------------------------------------------
verifyFile f =   
  do  p   <- parseNanoFromFile f
      cfg <- getOpts 
      verb    <- V.getVerbosity
      fmap (, "") <$> reftypeCheck cfg f (typeCheck verb (padTransform $ ssaTransform p))

-- DEBUG VERSION 
-- ssaTransform' x = tracePP "SSATX" $ ssaTransform x 

--------------------------------------------------------------------------------
reftypeCheck :: Config -> FilePath -> Nano AnnTypeR RefType -> IO (F.FixResult SourceSpan)
--------------------------------------------------------------------------------
reftypeCheck cfg f = solveConstraints f . generateConstraints cfg

--------------------------------------------------------------------------------
solveConstraints :: FilePath -> CGInfo -> IO (F.FixResult SourceSpan) 
--------------------------------------------------------------------------------
solveConstraints f cgi 
  = do (r, sol) <- solve def f [] $ cgi_finfo cgi
       let r'    = fmap (srcPos . F.sinfo) r
       renderAnnotations f sol r' $ cgi_annot cgi
       donePhase (F.colorResult r) (F.showFix r) 
       return r'

renderAnnotations srcFile sol res ann  
  = do writeFile   annFile  $ wrapStars "Constraint Templates" ++ "\n" 
       appendFile  annFile  $ ppshow ann
       appendFile  annFile  $ wrapStars "Inferred Types"       ++ "\n" 
       appendFile  annFile  $ ppshow ann'
       B.writeFile jsonFile $ A.annotByteString res ann' 
       donePhase Loud "Written Inferred Types"
    where 
       jsonFile = extFileName Json  srcFile
       annFile  = extFileName Annot srcFile
       ann'     = tidy $ applySolution sol ann

applySolution :: F.FixSolution -> A.AnnInfo RefType -> A.AnnInfo (RType F.Reft)
applySolution = fmap . fmap . tx
  where
    tx s (U (F.Reft (x, zs)) _)   = F.Reft (x, F.squishRefas (appSol s <$> zs))
    appSol _ ra@(F.RConc _) = ra 
    appSol s (F.RKvar k su) = F.RConc $ F.subst su $ M.lookupDefault F.PTop k s  

tidy = id

--------------------------------------------------------------------------------
generateConstraints     :: Config -> NanoRefType -> CGInfo 
--------------------------------------------------------------------------------
generateConstraints cfg pgm = getCGInfo cfg p . consNano $ p
  where
    p = pgm { defs  = {- envMap go $ -} defs pgm
            , specs = envMap go $ specs pgm
            }
    γ = tDefs pgm
    go = mapTys (appTVarArgs γ . addRefSorts γ . expandTApp γ)

addRefSorts :: REnv -> RefType -> RefType
addRefSorts γ t@(TApp c ts rs r)
  = TApp c ts rs' r'
  where
    rs'               = addRefSortsRef <$> zip ps trs
    ps                = typeRefArgs γ c
    (trs, rest)       = splitAt (length ps) rs
    r'                = foldl go r rest
    go r (PMono _ r') = r' `F.meet` r
    go r _            = r

addRefSorts _ t
  = t

appTVarArgs γ (TApp c ts rs r)
  = TApp c ts (apply θ rs) r
    where
      θ = fromLists (safeZip "appTVarArgs" (typeVarArgs γ c) ts) []

appTVarArgs _ t
  = t

addRefSortsRef (p, PPoly s (TVar v r)) | F.symbol v == F.dummySymbol
  = PPoly (safeZip "addRefSortsRefPoly" (fst <$> s) $ (fst3 <$> pv_as p)) t
    where t = ofType (pv_ty p) `strengthen` r
addRefSortsRef (p, PPoly s t)
  = PPoly (safeZip "addRefSortsRefPoly" (fst <$> s) $ (fst3 <$> pv_as p)) t
addRefSortsRef (p, PMono s r@(U _ (Pr [up])))
  = PMono (safeZip "addRefSortsRefMono" (snd3 <$> (pv_as $ traceShow "up" up)) (fst3 <$> (pv_as $ traceShow "p" p))) r
addRefSortsRef (_, m)
  = m

--------------------------------------------------------------------------------
consNano     :: NanoRefType -> CGM ()
--------------------------------------------------------------------------------
consNano pgm@(Nano {code = Src fs}) 
  = consStmts (initCGEnv pgm) fs >> return ()

  -- = forM_ fs . consFun =<< initCGEnv pgm
initCGEnv pgm = CGE defs heapEmpty F.emptyIBindEnv []
  where
    defs    = envUnion (specs pgm) $ tDefs pgm

--------------------------------------------------------------------------------
consFun :: CGEnv -> Statement (AnnType_ RReft) -> CGM CGEnv
--------------------------------------------------------------------------------
consFun g (FunctionStmt l f xs body) 
  = do ftDef          <- getDefType f
       γ              <- getTDefs
       ft             <- freshTyFun g l f ftDef
       g'             <- envAdds [(f, go γ ft)] g
       g''            <- envAddFun l g' f xs (go γ ft) >>= envAddNil l
       when (not $ isTrivialRefType ftDef) $ 
            subTypeFun l g'' ft ftDef
       withFun (F.symbol f) $
         do gm <- consStmts g'' body
            maybe (return ()) (\g -> subType l g tVoid (envFindReturn g'')) gm
            return g'
  where
    go γ = mapTys (appTVarArgs γ . addRefSorts γ . expandTApp γ)
    {-   msg = printf "freshTyFun f = %s" (ppshow f)-}

consFun _ _ = error "consFun called not with FunctionStmt"

subTypeFun l g f f' = subType' "subTypeFun" l g ft ft'
  where (_, _, ft) = bkAll f
        (_, _, ft') = bkAll f'

              
-----------------------------------------------------------------------------------
envAddFun :: AnnTypeR -> CGEnv -> Id AnnTypeR -> [Id AnnTypeR] -> RefType -> CGM CGEnv
-----------------------------------------------------------------------------------
envAddFun l g f xs ft
    = do (su', g') <- envAddHeap l g (applyPredsBind πs <$> h)
         let g''   =  envAddReturn f (F.subst su' . applyPreds πs $ b_type t') g'
         g'''      <- envAdds (envBinds su' xs ts') g''
         gαs       <- envAdds tyBinds g'''
         envAdds pBinds gαs
  where  
    (αs, πs, yts, h, _, t)  = mfromJust "envAddFun" $ bkFun ft
    pBinds                  = [(pv_sym π, toPredType π) | π <- πs]
    tyBinds                 = [(Loc (srcPos l) α, tVar α) | α <- αs]
    varBinds                = safeZip "envAddFun"
    envBinds su xs ts       = varBinds xs (applyPreds πs . F.subst su <$> ts)
    (su, ts')               = renameBinds yts xs
    t'                      = F.subst su <$> t

applyPredsBind πs b     = b { b_type = applyPreds πs $ b_type b }

applyPreds :: [PVar Type] -> RefType -> RefType
applyPreds πs t
    = foldl replacePred t πs
    where
      mkSub p         = (fmap (const ()) p, pVartoRConc p)
      replacePred t p = replacePredsWithRefs (mkSub p) <$>  t

envAddNil l g = snd <$> envAddHeap l g nilHeap
    where
      nilHeap = heapAdd "envAddNil" nilLoc nilBind heapEmpty

envAddHeap l g σ
  = do let xs           = b_sym <$> bs
       let (su, ts_pre) = renameBinds bs xs
           ts           = map (uncurry strengthenObjBinds) (zip xs ts_pre)
           σ'           = refHeapFromTyBinds "envAddHeap" (zip ls $ mkHeapBinds xs ts)
       -- (ts',g')        <- foldM foldFresh ([],g) ts
       let g'           = g { rheap = heapCombine "envAddHeap" [σ', rheap g] }
       g''            <- envAdds (varBinds xs ({- reverse $ -} (fmap F.top) <$> ts)) g'
       return (su, g'')
  where
    (ls,bs)            = unzip $ heapBinds σ
    varBinds           = safeZipWith "envAddHeap" (\x t -> (x, t `eSingleton` x))
    mkHeapBinds        = safeZipWith "envAddHeap" (\x t -> B x $ t `eSingleton` x)
    foldFresh (ts,g) t = freshObjBinds l g t >>= \(t',g') -> return (t':ts, g')

renameBinds yts xs   = (su, [F.subst su ty | B _ ty <- yts])
  where 
    su               = F.mkSubst $ safeZipWith "renameBinds" fSub yts xs 
    fSub yt x        = (b_sym yt, F.eVar x)
-- checkFormal x t 
--   | xsym == tsym = (x, t)
--   | otherwise    = errorstar $ errorArgName (srcPos x) xsym tsym
--   where 
--     xsym         = F.symbol x
--     tsym         = F.symbol t

--------------------------------------------------------------------------------
consStmts :: CGEnv -> [Statement AnnTypeR]  -> CGM (Maybe CGEnv) 
--------------------------------------------------------------------------------
consStmts = consSeq consStmt

--------------------------------------------------------------------------------
consStmt :: CGEnv -> Statement AnnTypeR -> CGM (Maybe CGEnv) 
--------------------------------------------------------------------------------

-- | @consStmt g s@ returns the environment extended with binders that are
-- due to the execution of statement s. @Nothing@ is returned if the
-- statement has (definitely) hit a `return` along the way.

-- skip
consStmt g (EmptyStmt _) 
  = return $ Just g

-- x = e
consStmt g (ExprStmt _ (AssignExpr _ OpAssign (LVar lx x) e))   
  = consAsgn g (Id lx x) e

-- e1.x = e2
consStmt g (ExprStmt _ (AssignExpr _ OpAssign (LDot l e3 x) e2))
  = do (x2,g2) <- consExpr g e2
       (x3,g3) <- consExpr g2 e3
       (_,g4)  <- consAccess l x3 g3 x
       -- The plan here: --
       --   1. Figure out the stored type (T_e2) (done)
       --   2. Find the referenced type, i.e. the object, Tobj
       --   3. create a NEW object with type Tobj' that is
       --      - Tobj' = Tobj { ... f:{ v = x2 } ... }
       --   4. create a NEW binder for Tobj'
       --   5. update the binder at l to this new binder
       --   6. instantiate any measures for the pointer
       let tref   = envFindTy x3 g4
           [m]    = locs tref  -- Assuming no unions of references
       -- (b, g5)    <- envFreshHeapBind l m g4 
       Just <$> updateFieldM l m g4 x x2

-- e
consStmt g (ExprStmt _ e)   
  = consExpr g e  >>= return . Just . snd 

-- s1;s2;...;sn
consStmt g (BlockStmt _ stmts) 
  = consStmts g stmts 

-- if b { s1 }
consStmt g (IfSingleStmt l b s)
  = consStmt g (IfStmt l b s (EmptyStmt l))

-- HINT: 1. Use @envAddGuard True@ and @envAddGuard False@ to add the binder 
--          from the condition expression @e@ into @g@ to obtain the @CGEnv@ 
--          for the "then" and "else" statements @s1@ and @s2 respectively. 
--       2. Recursively constrain @s1@ and @s2@ under the respective environments.
--       3. Combine the resulting environments with @envJoin@ 

-- if e { s1 } else { s2 }
consStmt g (IfStmt l e s1 s2)
  = do (xe, ge) <- consExpr g e
       g1'      <- (`consStmt` s1) $ envAddGuard xe True  ge 
       g2'      <- (`consStmt` s2) $ envAddGuard xe False ge
       envJoin l g g1' g2'

-- var x1 [ = e1 ]; ... ; var xn [= en];
consStmt g (VarDeclStmt _ ds)
  = consSeq consVarDecl g ds

-- return e 
consStmt g r@(ReturnStmt l (Just e))
  = do  b        <- getFunRetBinder g l
        (xe, g') <- consExpr g e
        (su, θi) <- consReturnHeap g' (Just (b, xe)) r
        let te    = F.subst su $ envFindTy xe g'
            rt    = F.subst su . apply θi $ envFindReturn g'
        g' <- envAdds [(xe, te)] g'
        if isTop rt
          then withAlignedM (subTypeContainers l g') te (setRTypeR te (rTypeR rt))
          else withAlignedM (subTypeContainers l g') te rt
        return Nothing

-- return
consStmt g r@(ReturnStmt l Nothing)
  = consReturnHeap g' Nothing r >> return Nothing 
  where           
    dels = concat [ ls | Delete ls <- ann_fact l ]
    g'   = g { rheap = heapFromBinds "consReturn" . filter ((`notElem` dels) . fst) . heapBinds $ rheap g
             , renv  = envMap (deleteLocsTy dels) $ renv g
             }

-- function f(x1...xn){ s }
consStmt g s@(FunctionStmt _ _ _ _)
  = Just <$> consFun g s
    
consStmt g (WindAll l _)    
  = Just <$> foldM (consWind l) g' ws
  where
    ws     = reverse [ (l, wls, t, fromLists αs ls)
                     | WindInst l wls t αs ls <- ann_fact l ]
    dels   = okDels $ concat [ ls | Delete ls <- ann_fact l ]
    okDels = filter (`notElem` (concat $ snd4 <$> ws))
    g'   = g { rheap = heapFromBinds "WindAll deletes" . filter ((`notElem` dels) . fst) . heapBinds $ rheap g
             , renv  = envMap (deleteLocsTy dels) $ renv g
             }

consStmt g (UnwindAll l _)    
  = Just <$> foldM (consUnwind l) g ws
  where
    ws = [ (l,t,fromLists [] ls) | UnwindInst l t ls <- ann_fact l ]
    
consStmt g (RenameLocs l _)    
   = Just <$> consRename l g θ
   where
     θ = head $ [ fromLists [] ls | Rename ls <- ann_fact l ]
    
-- OTHER (Not handled)
consStmt _ s 
  = errorstar $ "consStmt: not handled " ++ ppshow s

consReturnHeap :: CGEnv 
               -> Maybe (F.Symbol, Id AnnTypeR) 
               -> Statement AnnTypeR 
               -> CGM (F.Subst, RSubst RReft)
consReturnHeap g xro (ReturnStmt l _)
  = do (_,σ)         <- (apply θi <$>) <$> getFunHeaps g l
       let rsu       = F.mkSubst $ maybe [] (\(b,x) -> [(b, F.eVar $ F.symbol x)]) xro
       let (su,σ')   = renameHeapBinds (rheap g) (fmap (F.subst rsu) <$> refHeap $ tracePP "CONS RETURN HEAP" σ)
       let g'        = g { renv = envMap (F.subst su <$>) $ renv g }
       -- "Relax" subtyping checks on *new* locations in the output heap
       -- for all x with l \in locs(x), add x:<l> <: z:T, then do
       -- subtyping under G;x:T. (If all refs are _|_ then z:_|_)
       subTypeHeaps l g' (rheap g') (fmap (F.subst $ traceShow "RETURN HEAP SUB" su) <$> tracePP "CONS RETURN HEAP PRIME" σ')
       return (rsu `F.catSubst` su, θi)
    where
      θi = head $ [ fromLists [] ls | WorldInst ls <- ann_fact l ] :: RSubst RReft

consReturnHeap _ _ _ = error "BUG: consReturnHeap non-return"

getFunHeaps g _
  -- = (fromJust . funHeaps . flip envFindTy g) <$> getFun
  = do ft                         <- flip envFindTy g <$> getFun
       let (_, πs, _, h1, h2, _)  = mfromJust "getFunHeaps" $ bkFun ft
       return $ mapPair (applyPredsBind πs <$>) (h1, h2)

getFunRetBinder g _
  = (retBind . fromJust . bkFun . flip envFindTy g) <$> getFun
  where
    retBind (_,_,_,_,_,b) = b_sym $ b


------------------------------------------------------------------------------------
consVarDecl :: CGEnv -> VarDecl AnnTypeR -> CGM (Maybe CGEnv) 
------------------------------------------------------------------------------------

consVarDecl g (VarDecl _ x (Just e)) 
  = consAsgn g x e  

consVarDecl g (VarDecl _ _ Nothing)  
  = return $ Just g

------------------------------------------------------------------------------------
consAsgn :: CGEnv -> Id AnnTypeR -> Expression AnnTypeR -> CGM (Maybe CGEnv) 
------------------------------------------------------------------------------------
consAsgn g x e 
  = do (x', g') <- consExpr g e
       Just <$> envAdds [(x, envFindTy x' g')] g'

------------------------------------------------------------------------------------
consExpr :: CGEnv -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv) 
------------------------------------------------------------------------------------

-- | @consExpr g e@ returns a pair (g', x') where
--   x' is a fresh, temporary (A-Normalized) variable holding the value of `e`,
--   g' is g extended with a binding for x' (and other temps required for `e`)

consExpr g (DownCast a e) 
  = do  (x, g') <- consExpr g e
        consDownCast g' x a e 

consExpr g (UpCast a e)
  = do  (x, g') <- consExpr g e
        consUpCast g' x a e

consExpr g (DeadCast a e)
  = consDeadCast g a e

consExpr g (IntLit l i)               
  = envAddFresh l (eSingleton tInt i) g

consExpr g (BoolLit l b)
  = envAddFresh l (pSingleton tBool b) g 

consExpr g (StringLit l s)
  = envAddFresh l (eSingleton tString s) g

consExpr g (NullLit l)
  = envAddFresh l tNull g

consExpr g (VarRef i x)
  = do addAnnot l x t
       return (x, g) 
    where 
       t           = envFindTy x g
       l           = srcPos i

consExpr g (PrefixExpr l o e)
  = consCall g l o [e] (prefixOpTy o $ renv g)

consExpr g (InfixExpr l o e1 e2)        
  = consCall g l o [e1, e2] (infixOpTy o $ renv g)

consExpr g (CallExpr l e es)
  = do (x, g') <- consExpr g e 
       consCall g' l e es $ envFindTy x g'

consExpr  g (DotRef l e i)
  = do  (x, g')   <- consExpr g e
        consAccess l x g' i

consExpr  g (BracketRef l e (StringLit _ s))
  = do  (x, g') <- consExpr g e
        consAccess l x g' s

consExpr g (ObjectLit l ps) 
  = consObj l g ps

consExpr _ e 
  = error $ (printf "consExpr: not handled %s" (ppshow e))


---------------------------------------------------------------------------------------------
consAccess :: (F.Symbolic s, F.Symbolic x, F.Expression x, IsLocated x, PP s) =>
               AnnTypeR -> x -> CGEnv -> s -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
-- In cons access we can now *strengthen* the *local* type of x when l |-> x:T in the heap
consAccess l x g i = do [(j,t)] <- dotAccessM l g i tp
                        g'      <- if (isConc "consAccess" j σ) then
                                     return g
                                   else
                                     concretizeLoc "consAccess" j g
                        envAddFresh l t g'
  where 
    tp  = envFindTy x g
    σ   = rheap g
              
dotAccessM l g f u@(TApp TUn _ _ _)
  = do concat <$> mapM dotAccessStrongEnv ts'
  where (TApp TUn ts' _ _)     = strengthenUnion u 
        dotAccessStrongEnv t = do (_, g') <- envAddFresh l t g 
                                  dotAccessM l g' f t


dotAccessM _ g f t@(TApp (TRef l) _ _ _)
  = do γ <- getTDefs
       let (x,t',σ) = refHeapMakeConc "dotAccessM" l (rheap g)
           results = fromJust $ dotAccessRef (γ, locTy g <$> rheap g) f t
       return $ [(l, foldl1 ((fst4.) . compareTs γ) (map ac_result results))]


dotAccessM l g _ _ = 
  subTypeContainers l g tru fls >> return []
  where 
    tru = tTop
    fls = tTop `strengthen` (ureft $ F.predReft F.PFalse)

------------------------------------------------------------------------------------------
consUpCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
------------------------------------------------------------------------------------------
consUpCast g x a e 
  = do  γ     <- getTDefs
        let b' = fst $ alignTs γ b u
        envAddFresh l (b' `strengthen` (ureft $ rTypeReft b)) g
  where 
    u          = rType $ head [ t | Assume t <- ann_fact a]
    b          = envFindTy x g 
    l          = getAnnotation e
      

-- No fresh K-Vars here - instead keep refs from original type
---------------------------------------------------------------------------------------------
consDownCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
consDownCast g x a e = 
  do γ   <- getTDefs
     tc  <- castTo (srcPos l) γ te τ 
     g'  <- envAdds [(x, tc)] g
     withAlignedM (subTypeContainers l g) te tc
     envAddFresh l tc g'
  where 
     τ    = toType $ head [ t | Assume t <- ann_fact a]
     te   = envFindTy x g
     l    = getAnnotation e

-- castTo               :: Env RefType -> Locate RType r -> Type -> RType r
castTo _ γ t τ       = castStrengthen t . zipType2 γ (++) botJoin t <$> bottify τ 
  where 
    bottify          = fmap (fmap F.bot) . true . rType 
    botJoin r1 r2 
      | F.isFalse (ur_reft r1) = r2
      | F.isFalse (ur_reft r2) = r1
      | otherwise    = error msg
    msg              = printf "botJoin: t = %s τ = %s" (ppshow (t :: RefType)) (ppshow (τ :: Type))

castStrengthen t1 t2 
  | isUnion t1 && not (isUnion t2) = t2 `strengthen` (ureft $ rTypeReft t1)
  | otherwise                      = t2

---------------------------------------------------------------------------------------------
consDeadCast :: CGEnv -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
consDeadCast g a e =
  do subTypeContainers l g tru fls
     envAddFresh l tC g
  where
    tC  = rType $ head [ t | Assume t <- ann_fact a]      -- the cast type
    l   = getAnnotation e
    tru = tTop
    fls = strengthen tTop . ureft $ F.predReft F.PFalse


---------------------------------------------------------------------------------------------
consCall :: (PP a) 
         => CGEnv -> AnnTypeR -> a -> [Expression AnnTypeR] -> RefType -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------

--   1. Fill in @instantiate@ to get a monomorphic instance of @ft@ 
--      i.e. the callee's RefType, at this call-site (You may want 
--      to use @freshTyInst@)
--   2. Use @consExpr@ to determine types for arguments @es@
--   3. Use @subTypes@ to add constraints between the types from (step 2) and (step 1)
--   4. Use the @F.subst@ returned in 3. to substitute formals with actuals in output type of callee.

consCall g l fn es ft 
  = do (_,_,its,hi',ho',ot) <- mfromJust "consCall" . bkFun <$> (tracePP ("FOFOFOFO: " ++ ppshow fn) <$> instantiate l g ft)
       (xes, g')            <- consScan consExpr (tracePP "consCall in" g) es
       let (argSu, ts')      = renameBinds its xes
           (heapSu, hi'')    = renameHeapBinds (rheap g') (refHeap hi')
           su                = heapSu `F.catSubst` argSu
           σin               = rheap g'
       -- Substitute binders in spec with binders in actual heap
       zipWithM_ (withAlignedM $ subTypeContainers l g') [envFindTy x g' | x <- xes] (F.subst su ts')
       subTypeHeaps l g' σin (F.subst su <$> hi'')
       let hu                = foldl (flip heapDel) (rheap g') $ heapLocs hi''
       (_,g'')              <- envAddHeap l (g' { rheap = hu }) (fmap (F.subst su) <$> ho')
       let lost  = deletedLocs σin $ rheap g''
           B rs rt = fmap (F.subst su) ot
           g'''  = g'' { renv  = renv g''
                       , rheap = heapFromBinds "consCall" . filter ((`notElem` lost) . fst) . heapBinds . rheap $ g''
                       }
       g_out                <- topMissingBinds g''' (rheap g') hi' >>= envAdds [(rs, rt)]
       g_outms              <- foldM (flip applyLocMeasEnv) g_out $ heapLocs hi'
       return (Id l $ F.symbolString rs, tracePP "consCall outms" g_outms)
              
{- 
A binder may only be brought into the local context (i.e. gamma) under
the constraint that it is NIL if unreachable
-}
deletedLocs σi σo = filter (`notElem` heapLocs σo) $ heapLocs σi         

topMissingBinds g σ σenv
  = envAdds (zip bs $ repeat tTop) g
    where ls = filter (`notElem` heapLocs σ) $ heapLocs σenv
          bs = map (b_sym . rd) ls
          rd l = heapRead "topMissingBinds" l σenv

instantiate :: AnnTypeR -> CGEnv -> RefType -> CGM RefType
instantiate l g t 
  = do γ   <- getTDefs 
       let tbody'' = go γ tbody'
       tαs <- freshTyInst l g αs τs tbody''
       freshPredInst l g πs tαs
  where 
    go γ            = mapTys (appTVarArgs γ . addRefSorts γ . expandTApp γ)
    tbody'          = apply θl tbody
    (αs, πs, tbody) = bkAll t
    τs              = map snd ts
    θl              = fromLists [] ls :: RSubst RReft
    (ts,ls)         = head [ (ts,ls) | FunInst ts ls <- ann_fact l ]

---------------------------------------------------------------------------------
consScan :: (CGEnv -> a -> CGM (b, CGEnv)) -> CGEnv -> [a] -> CGM ([b], CGEnv)
---------------------------------------------------------------------------------
consScan step g xs  = go g [] xs 
  where 
    go g acc []     = return (reverse acc, g)
    go g acc (x:xs) = do (y, g') <- step g x
                         go g' (y:acc) xs

---------------------------------------------------------------------------------
consSeq  :: (CGEnv -> a -> CGM (Maybe CGEnv)) -> CGEnv -> [a] -> CGM (Maybe CGEnv) 
---------------------------------------------------------------------------------
consSeq f           = foldM step . Just 
  where 
    step Nothing _  = return Nothing
    step (Just g) x = f g x


---------------------------------------------------------------------------------
consObj :: AnnTypeR -> CGEnv -> [(Prop AnnTypeR, Expression AnnTypeR)] -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------
consObj l g pe = 
  do
    let (ps, es) = unzip pe
    (xes, g1)   <- consScan consExpr g es
    let pxs      = zipWith B (map F.symbol ps) $ map (flip envFindTy g1) xes
    let tptr     = TApp (TRef loc) [] [] mempty
    (x, g2)     <- envFreshHeapBind l loc g1
    let tob_pre  = TObj pxs mempty
    -- This creates binders in the envt for each field
    (tob, g3)   <- freshObjBinds l g2 (x `strengthenObjBinds` tob_pre)
    g4          <- envAdds [(x,tob)] g3
    (i, g5)     <- envAddFresh l tptr g4
    return (i,g5)
  where          
    loc = head [ l | LocInst l <- ann_fact l]
    
---------------------------------------------------------------------------------
consWind :: AnnTypeR -> CGEnv -> (Location, [Location], Id SourceSpan, RSubst RReft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consWind l g (m, wls, ty, θ)
  -- What needs to be done here:
  -- Given the instantiation θ:
  -- Instantiate C[α] and add a new binder. oh wait, that is fairly easy...
  = do (σenv, (x,tw), t, ms) <- freshConsWind g l θ ty m
       let xts               = toIdTyPair <$> heapTypes (tracePP "SIG ENV" σenv)
           g'                = g { rheap =  heapDiff (rheap g) (m:wls) }
           r                 = instMeasures [F.vv Nothing] ms
       g_st                 <- envAdds xts g
       (g_st, su)           <- envAddFieldBinders l x tw g_st
       (z, g'')             <- envFreshHeapBind l m g'
       g'''                 <- envAdds [(z, strengthen t r)]  g''
       subTypeWind l (tracePP "g_st" g_st) ((F.subst su <$>) <$> σenv) (hpRead g_st m (rheap g_st)) (F.subst su tw)
       -- subTypeWind l (tracePP "g_st" g_st) σenv (hpRead g_st m (rheap g_st)) tw
       applyLocMeasEnv m g'''
       where
         hpRead g      = heapReadType g "consWind"
         s             = srcPos l
         toIdTyPair b  = (Id s (F.symbolString $ locSym b), locTy emptyCGEnv b)
         heapDiff σ ls = foldl (flip heapDel) σ ls
                         
freshConsWind g l θ ty m
    = do (σenv, (x,tw), t, ms) <- freshTyWind g l θ ty
         let xsu         = F.mkSubst [(x, F.eVar x')]
             (hsu,σenv') = renameHeapBinds (rheap g) σenv
             su          = F.catSubst xsu hsu
             σenv''      = fmap (F.subst su) <$> σenv'
             tw'         = F.subst su tw
             t'          = F.subst su t
             ms'         = subMeas su <$> ms 
         return (σenv'', (x',tw'), t', ms')
    where
      x'                  = hpRead m (rheap g)
      subMeas su (f,as,e) = (f, as, F.subst su e)
      hpRead              = heapReadSym "freshConsWind"

---------------------------------------------------------------------------------
consUnwind :: AnnTypeR -> CGEnv -> (Location, Id SourceSpan, RSubst RReft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consUnwind l g (m, ty, θl) =
  do 
    (σ,s,t,αs,πs)  <- envFindTyDef ty
    g              <- if (isConc "consAccess" m $ rheap g) then
                         return g
                       else
                         seq (tracePP "FIX ME" "sketchy") concretizeLoc "consAccess" m g
    (σ',t',hsu)    <- unwindInst l (unwindTyApp l g m αs) θl πs (rs g) (σ, t)
    ms             <- getRMeasures ty
    (s',g')        <- envFreshHeapBind l m g
                      
    (g', bsu)      <- envAddFieldBinders l s' t' g'
 
    let r           = instRMeas su (F.symbol b) ms
        σ''         = tracePP "CONS UNWIND c" (instPropBind r . subst su <$> σ')
        su          = bsu `F.catSubst` hsu `F.catSubst` sub1 s s'
    (_, g'')       <- envAddHeap l g' σ''
    g'''           <- envAdds [(s', mapTys (flip strengthen r) $ subst su $ strengthenObjBinds s' t')] g''
    gm             <- applyLocMeasEnv m g'''
    -- Add "witness" for each type variable??
    foldM (envAdd l) gm $ apply (unwindTyApp l g m αs) (tVar <$> αs)
  where
    envAdd l g t = snd <$> envAddFresh l t g
    rs g         = unwindTyRefs $ envFindTy b g
    subst su     = fmap $ F.subst su
    sub1 x y     = F.mkSubst [(F.symbol x, F.eVar y)]
    b            = heapReadSym "consUnwind" m (rheap g)
  
instPropBind r (B x t) = B x $ strengthen t r

instRMeas su b' ms 
  = F.subst su $ instMeasures [b'] ms

unwindTyRefs (TApp _ _ rs _)
  = rs
unwindTyRefs t
  = error $ printf "BUG: Unwinding unexpected %s" (ppshow t)

unwindTyApp l g m αs
  = flip fromLists [] $ zip αs vs
    where
      -- msg   = "%s BUG: unwound something bad! %s"
      err p = error $ printf (ppshow (srcPos l)) (ppshow p)
      vs    = case heapReadType g "consUnwind" m (rheap g) of
                TApp _ vs _ _  -> vs
                p              -> err p

unwindInst l θα θl πs rs (σ,t)
  = do (su, σ'') <- freshHeapEnv l $ tracePP "UNWIND INST SIG PRIME" σ'
       γ         <- getTDefs
       return (replBi γ <$> σ'', repl γ t', su)
  where 
    θ      = θl <> θα
    σ'     = apply θ σ
    t'     = apply θ t
    rsu    = zip (traceShow "PIS" πs) (tracePP "RS" $ apply θ rs)
    repl γ = flip replacePreds rsu . expandTApp γ
    replBi γ (B x t) = B x $ repl γ t

consRename _ _ _
  = error "consRename"

applyLocMeasEnv l g
    = do xts' <- mapM (fmap debind . addMeasuresM g) xts
         envAdds xts' g
    where
      debind (B x t) = (x, t)
      xts    = [ B (F.symbol x) t | (x, t) <- e, l `elem` locs t ]
      e      = envToList g

deleteLoc l g ls t = do
  t' <- refresh $ deleteLocsTy ls t
  constrain t t'
  return t'
  where constrain t t' | isUnion t = subTypeContainers l g (setRTypeR t mempty) t'
        constrain t t' | otherwise = subTypeContainers l g t t'
