{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}

-- | Top Level for Refinement Type checker

-- module Language.Nano.Liquid.Liquid (verifyFile) where
module Language.Nano.Liquid.Liquid  where

import           Text.Printf                        (printf)
-- import           Text.PrettyPrint.HughesPJ          (Doc, text, render, ($+$), (<+>))
import           Control.Monad
import           Control.Applicative                ((<$>))

import qualified Data.ByteString.Lazy               as B
import qualified Data.HashMap.Strict                as M
import           Data.Maybe                         (fromJust)
import           Data.Monoid
import           Data.List

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
-- import           Language.Nano.Typecheck.WindFuns
import           Language.Nano.Typecheck.Parse
import           Language.Nano.Typecheck.Subst
import           Language.Nano.Typecheck.Typecheck  (typeCheck) 
import           Language.Nano.Typecheck.Compare
import           Language.Nano.SSA.SSA
import           Language.Nano.Liquid.Types
import           Language.Nano.Liquid.CGMonad
import           Language.Nano.Misc

import           System.Console.CmdArgs.Default

-- import           Debug.Trace                        (trace)

import qualified System.Console.CmdArgs.Verbosity as V

--------------------------------------------------------------------------------
verifyFile       :: FilePath -> IO (F.FixResult (SourceSpan, String))
--------------------------------------------------------------------------------
verifyFile f =   
  do  p   <- parseNanoFromFile f
      cfg <- getOpts 
      verb    <- V.getVerbosity
      fmap (, "") <$> reftypeCheck cfg f (typeCheck verb (ssaTransform p))

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

applySolution :: F.FixSolution -> A.AnnInfo RefType -> A.AnnInfo RefType 
applySolution = fmap . fmap . tx
  where
    tx s (F.Reft (x, zs))   = F.Reft (x, F.squishRefas (appSol s <$> zs))
    appSol _ ra@(F.RConc _) = ra 
    appSol s (F.RKvar k su) = F.RConc $ F.subst su $ M.lookupDefault F.PTop k s  

tidy = id

--------------------------------------------------------------------------------
generateConstraints     :: Config -> NanoRefType -> CGInfo 
--------------------------------------------------------------------------------
generateConstraints cfg pgm = getCGInfo cfg pgm $ consNano pgm

--------------------------------------------------------------------------------
consNano     :: NanoRefType -> CGM ()
--------------------------------------------------------------------------------
consNano pgm@(Nano {code = Src fs}) 
  = consStmts (initCGEnv pgm) fs >> return ()

  -- = forM_ fs . consFun =<< initCGEnv pgm
initCGEnv pgm = CGE defs heapEmpty F.emptyIBindEnv []
  where
    defs = envUnion (specs pgm) $ tDefs pgm

--------------------------------------------------------------------------------
consFun :: CGEnv -> Statement (AnnType_ F.Reft) -> CGM CGEnv
--------------------------------------------------------------------------------
consFun g (FunctionStmt l f xs body) 
  = do ft             <- freshTyFun g l f =<< getDefType f
       g'             <- envAdds [(f, ft)] g 
       g''            <- envAddFun l g' f xs ft
       withFun (F.symbol f) $
         do gm <- consStmts g'' body
            maybe (return ()) (\g -> subType l g tVoid (envFindReturn g'')) gm
            return g'
    {-where -}
    {-   msg = printf "freshTyFun f = %s" (ppshow f)-}

consFun _ _ = error "consFun called not with FunctionStmt"

-----------------------------------------------------------------------------------
envAddFun :: AnnTypeR -> CGEnv -> Id AnnTypeR -> [Id AnnTypeR] -> RefType -> CGM CGEnv
-----------------------------------------------------------------------------------
envAddFun l g f xs ft
    = do (su', g') <- envAddHeap l g h
         ts''      <- tracePP "envAddFun" <$> mapM (\t -> addHeapMeasures g' (rTypeValueVar t, t)) ts'
         g''       <- envAdds (envBinds su' xs ts'') =<< (return $ envAddReturn f (F.subst su' t') g')
         envAdds tyBinds g''
  where  
    (αs, yts, h, _, t)  = mfromJust "envAddFun" $ bkFun ft
    tyBinds             = [(Loc (srcPos l) α, tVar α) | α <- αs]
    varBinds            = safeZip "envAddFun"
    envBinds su xs ts   = varBinds xs (F.subst su <$> ts)
    (su, ts')           = renameBinds yts xs
    t'                  = F.subst su t
    -- g'                  = g { rheap = F.subst su h }

envAddHeap l g σ
  = do xs              <- mapM (return . Id (srcPos l) . F.symbolString . b_sym) bs
       let (su, ts_pre) = renameBinds bs xs
           ts           = map (uncurry strengthenObjBinds) (zip xs ts_pre)
           σ'           = heapFromBinds "envAddHeap" (zip ls xs)
       (ts',g')        <- foldM foldFresh ([],g) ts
       g''             <- envAdds (varBinds xs (reverse ts')) g'
       return (su, g'' { rheap = heapCombine "envAddHeap" [σ', rheap g''] })
  where
    (ls,bs)            = unzip $ heapBinds σ
    varBinds           = safeZipWith "envAddHeap" (\x t -> (x, t `eSingleton` x))
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
consStmt g (ExprStmt _ (AssignExpr l2 OpAssign (LDot l e3 x) e2))
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
       let σ      = rheap g4
           tref   = envFindTy x3 g4
           [m]    = locs tref  -- Assuming no unions of references
       (b, g5)     <- envFreshHeapBind l m g4 
       Just <$> updateFieldM l g5 (heapRead "e1.x = e2" m σ) b x x2

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
  = do  (xe, g') <- consExpr g e
        (su, θi) <- tracePP "ReturnStmt" (rheap g')`seq`consReturnHeap g' (Just xe) r
        let te    = F.subst su $ envFindTy xe g'
            rt    = F.subst su . apply θi $ envFindReturn g'
            tok   = tracePP (printf "ReturnStmt (su = %s)" (show su)) (te, rt)
        g' <- envAdds [(xe, te)] g'
        if isTop rt
          then withAlignedM (subTypeContainers l g') te (setRTypeR te (rTypeR rt))
          else tok`seq`withAlignedM (subTypeContainers' "Return" l g') te rt
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
  = Just <$> foldM (consWind l) (g'{ rheap = app θm $ rheap g'} ) ws
  where
   --- Shouldn't have to do this here, move me!!! --
    θm = case [fromLists [] ls | Rename ls <- ann_fact l ] of
                  [θ] -> mempty :: RSubst F.Reft
                  _   -> mempty
    -------------------------------------------------
    ws     = reverse [ (apply θm l, apply θm wls, t, fromLists αs ls)
                     | WindInst l wls t αs ls <- ann_fact l ]
    dels   = okDels $ concat [ ls | Delete ls <- ann_fact l ]
    okDels = filter (`notElem` (concat $ snd4 <$> ws))
    app θ  = heapFromBinds "WindAll" . map (\(l,x) -> (apply θ l, x)) . heapBinds
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

lqretSymbol = F.symbol "lqreturn"

consReturnHeap :: CGEnv -> Maybe (Id AnnTypeR) -> Statement AnnTypeR -> CGM (F.Subst, RSubst F.Reft)
consReturnHeap g xro (ReturnStmt l _)
  = do (σi,σ)       <- (apply θi <$>) <$> getFunHeaps g l
       let rsu       = F.mkSubst $ maybe [] (\x -> [(F.symbol "lqreturn", F.eVar $ F.symbol x)]) xro
       let (su,σ')   = fmap b_type <$> renameHeapBinds (rheap g) (fmap (F.subst rsu <$>) σ)
       let g'        = g { renv = envMap (F.subst su <$>) $ renv g }
       -- "Relax" subtyping checks on *new* locations in the output heap
       -- for all x with l \in locs(x), add x:<l> <: z:T, then do
       -- subtyping under G;x:T. (If all refs are _|_ then z:_|_)
       subTypeHeaps l g' (flip envFindTy g' <$> rheap g') (fmap (F.subst su) <$> σ')
       return (rsu `F.catSubst` su, θi)
    where
      θi = head $ [ fromLists [] ls | WorldInst ls <- ann_fact l ] :: RSubst F.Reft


getFunHeaps g _
  = (fromJust . funHeaps . flip envFindTy g) <$> getFun


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
       t' <- addHeapMeasures g (rTypeValueVar t, t)
       g' <- envAdds [(x, t')] g
       return ({- trace ("consExpr:VarRef" ++ ppshow x ++ " : " ++ ppshow t)-} x, tracePP "VarRef g" g') 
    where 
       t           = tracePP (printf "findTy %s" (ppshow x)) $ envFindTy x g
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
consAccess l x g i = do [(_,t)]          <- dotAccessM l g i $ envFindTy x g
                        envAddFresh l t g
              
dotAccessM l g f u@(TApp TUn _ _)
  = do concat <$> mapM dotAccessStrongEnv ts'
  where (TApp TUn ts' _)     = strengthenUnion u 
        dotAccessStrongEnv t = do (_, g') <- envAddFresh l t g 
                                  dotAccessM l g' f t


dotAccessM _ g f t@(TApp (TRef l) _ _)
  = do γ <- getTDefs
       let results = fromJust $ dotAccessRef (γ, flip envFindTy g <$> rheap g) f t
       return $ [(l, foldl1 ((fst4.) . compareTs γ) (map ac_result results))]


dotAccessM l g _ _ = 
  subTypeContainers' "dead access" l g tru fls >> return []
  where 
    tru = tTop
    fls = tTop `strengthen` F.predReft F.PFalse

------------------------------------------------------------------------------------------
consUpCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
------------------------------------------------------------------------------------------
consUpCast g x a e 
  = do  γ     <- getTDefs
        let b' = fst $ alignTs γ b u
        envAddFresh l (b' `strengthen` rTypeReft b) g
  where 
    u          = rType $ head [ t | Assume t <- ann_fact a]
    b          = envFindTy x g 
    l          = getAnnotation e
      

-- No fresh K-Vars here - instead keep refs from original type
---------------------------------------------------------------------------------------------
consDownCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
consDownCast g x a e 
  = do  g'  <- envAdds [(x, tc)] g
        withAlignedM (subTypeContainers' "Downcast" l g) te (rType tc)
        return (x, g')
        -- envAddFresh l tc g'
    where 
        tc   = head [ t | Assume t <- ann_fact a]
        te   = envFindTy x g
        l    = getAnnotation e


---------------------------------------------------------------------------------------------
consDeadCast :: CGEnv -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
consDeadCast g a e =
  do  subTypeContainers' "dead" l g tru fls
      envAddFresh l tC g
  where
    tC  = rType $ head [ t | Assume t <- ann_fact a]      -- the cast type
    l   = getAnnotation e
    tru = tTop
    fls = tTop `strengthen` F.predReft F.PFalse


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

consCall g l _ es ft 
  = do (_,its,hi',ho',ot) <- mfromJust "consCall" . bkFun <$> instantiate l g ft
       (xes, g')          <- consScan consExpr g es
       let (argSu, ts')   = renameBinds its xes
           (heapSu, hi'') = fmap b_type <$> renameHeapBinds (rheap g') hi'
           su             = heapSu `F.catSubst` argSu
           gin            = (flip envFindTy g') <$> rheap g'
       -- Substitute binders in spec with binders in actual heap
       zipWithM_ (withAlignedM $ subTypeContainers' "call" l g') [envFindTy x g' | x <- xes] (F.subst su ts')
       subTypeHeaps l g' gin (F.subst su <$> hi'')
       let hu  = foldl (flip heapDel) (rheap g') $ heapLocs hi''

       -- Substitute binder for return value in output heap
       (xr, g'')         <- envAddFresh l (tracePP "consCall ot" $ F.subst su ot) g'
       let rsu           = F.mkSubst [(lqretSymbol, F.eVar xr)]
       (_,g'')           <- envAddHeap l (g'' { rheap = hu }) (fmap (F.subst (su `F.catSubst` rsu)) <$> ho')

       let lost  = deletedLocs gin $ rheap g''
       let g'''  = g'' { renv  = envMap (deleteLocsTy lost) $ renv g''
                       , rheap = heapFromBinds "consCall" . filter ((`notElem` lost) . fst) . heapBinds . rheap $ g''
                       }
       g_out             <- topMissingBinds g''' (rheap g') hi'
       return (xr, g_out)
                                        
     {- where
         msg xes its = printf "consCall-SUBST %s %s" (ppshow xes) (ppshow its)-}

deletedLocs σi σo = filter (`notElem` heapLocs σo) $ heapLocs σi         

topMissingBinds g σ σenv
  = do envAdds (zip bs (repeat tTop)) g
    where ls = filter (`notElem` heapLocs σ) $ heapLocs σenv
          bs = map (b_sym . rd) ls
          rd l = heapRead "topMissingBinds" l σenv

instantiate :: AnnTypeR -> CGEnv -> RefType -> CGM RefType
instantiate l g t 
  = {-  tracePP msg  <$>  -} freshTyInst l g αs τs $ apply θl tbody
  where 
    (αs, tbody) = bkAll t
    τs          = map snd ts
    θl          = fromLists [] ls :: RSubst F.Reft
    (ts,ls)     = head [ (ts,ls) | FunInst ts ls <- ann_fact l ]
    {-msg           = printf "instantiate [%s] %s %s" (ppshow $ ann l) (ppshow αs) (ppshow tbody)-}

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
    let tptr     = TApp (TRef loc) [] F.top
    (x, g2)     <- envFreshHeapBind l loc g1
    let tob_pre  = TObj pxs F.top    
    -- This creates binders in the envt for each field
    (tob, g3)   <- freshObjBinds l g2 (x `strengthenObjBinds` tob_pre)
    (i, g4)     <- envAddFresh l tptr g3
    g5          <- envAdds [(x,tob)] g4
    return       $ {- trace (printf "Adding: %s :: %s" (ppshow i) (ppshow tob)) -} (i,g5)
  where          
    loc = head [ l | LocInst l <- ann_fact l]
    
---------------------------------------------------------------------------------
consWind :: AnnTypeR -> CGEnv -> (Location, [Location], Id SourceSpan, RSubst F.Reft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consWind l g (m, wls, ty, θ)
  -- What needs to be done here:
  -- Given the instantiation θ:
  -- Instantiate C[α] and add a new binder. oh wait, that is fairly easy...
  = do (σenv, (x,tw), t, ms) <- freshTyWind g l θ ty
       let xts               = (fmap (F.subst xsu) . toIdTyPair) <$> heapTypes σenv'
           xsu               = F.mkSubst [(F.symbol x, F.eVar x')]
           σw                = toId <$> σenv'
           (hsu, σenv')      = renameHeapBinds (rheap g) σenv
           g'                = g { rheap =  heapDiff (rheap g) (m:wls) }
           x'                = hpRead m (rheap g)
           v                 = rTypeValueVar t
           wls'              = filter (`elem` (heapLocs (rheap g))) (wls)
           su                = F.mkSubst $ zip (map (F.symbol . flip hpRead σw) wls') (map (F.eVar . flip hpRead (rheap g)) wls')
           ms'               = map (\(x,y,p) -> (x,y,F.subst su p)) ms
           p                 = F.predReft . F.PAnd . map (instProp v x' x) $ ms'
       g_st                 <- envAdds xts g
       subTypeWind l g_st σw (snd $ safeRefReadHeap "consWind" g_st (rheap g_st) m) $ F.subst hsu tw
       (z, g'')             <- envAdds xts g' >>= envFreshHeapBind l m
       envAdds [(z, F.subst hsu $ strengthen t p)]  g''
       where
         hpRead        = heapRead "consWind"
         s             = srcPos l
         toId          = Id s . F.symbolString . b_sym                      
         toIdTyPair b  = (toId b, b_type b)
         heapDiff σ ls = foldl (flip heapDel) σ ls

---------------------------------------------------------------------------------
consUnwind :: AnnTypeR -> CGEnv -> (Location, Id SourceSpan, RSubst F.Reft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consUnwind l g (m, ty, θl) =
  do 
    (σ,s,t,αs)  <- envFindTyDef ty
    (su,σ')     <- freshHeapEnv l σ
    ms          <- getMeasures ty
    (b,g')      <- envFreshHeapBind l m g
    let θ       = θl `mappend` fromLists (zip αs vs) []
        t'      = apply θ t
        σ''     = apply θ σ'
        v       = F.symbol $ heapRead "consUnwind v" m (rheap g)
        ms'     = map (\(x,y,p) -> (x,y,F.subst su p)) ms
        p       = F.predReft . F.PAnd . map (instProp v b s) $ ms'
        σ'''    = instPropBind p . (F.subst (F.mkSubst [(F.symbol s, F.eVar b)]) <$>) <$> σ''
    g''         <- envAdds [(b, strengthenObjBinds b $ F.subst su <$> t')] g'
    (_, g''')   <- envAddHeap l g'' σ'''
    return $ g'''
  where 
    vs = case safeRefReadHeap "consUnwind" g (rheap g) m of
           (_,TApp _ vs _)  -> vs
           p                -> error (printf "%s BUG: unwound something bad! %s" (ppshow (srcPos l)) (ppshow p))
    
instPropBind prop (B x t) = B x $ strengthen t prop

instProp z x' x = mkProp . instMeas (F.symbol z) (F.mkSubst [(F.symbol x, F.eVar x')])
    where      
      mkProp (i,v,e)           = F.PAtom F.Eq (F.EApp i [F.eVar v]) e 
      instMeas v' su (i, v, e) = (i, v', F.subst su $ F.subst (F.mkSubst [(v',F.eVar v)]) e)

addHeapMeasures g (x, TApp TUn ts r)
  = do ts' <- mapM (\t -> addHeapMeasures g (tracePP "addHeapMeasure vv" $ rTypeValueVar $ tracePP "addHeapMeasure t" t, t)) ts
       return $ TApp TUn ts' r                    

addHeapMeasures g (x, t@(TApp (TRef l) [] (F.Reft (vv,_))))
  = instHeapMeasures (tracePP "addHeapMeasure vv" $ vv, t) $ heapRead "addHeapMeasures"  l $ rheap g

addHeapMeasures _ (_, t)
  = return t                

instHeapMeasures (x,t) b
  = do hms <- heapMeasures <$> getMeasureImpls
       let pred = F.PAnd $ map (instHeapMeasure (F.vv Nothing) b) hms
       let p = tracePP "instHeapMeasures reft" (show $ rTypeReft t) `seq`F.predReft pred
       return $ tracePP "instHeapMeasures out" (tracePP "instHeapMeasures in t" t `strengthen` tracePP "instHeapMeasures p" p)
    where
      heapMeasures hms = [(m,x,b,body) | (m, ([x,b], body)) <- hms]              

instHeapMeasure x' b' (m,x,b,body)
  = tracePP "instHeapMeasure sub" (show su) `seq` F.PAtom F.Eq lhs rhs
    where su  = F.mkSubst [(x, F.eVar x'), (b, F.eVar b')]
          lhs = F.EApp m [F.eVar x', F.eVar b']
          rhs = F.subst su body

consRename _ _ _
  = error "consRename"
