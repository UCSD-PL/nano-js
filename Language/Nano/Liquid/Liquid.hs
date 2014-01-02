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
generateConstraints cfg pgm = getCGInfo cfg pgm $ consNano pgm

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
  = do ft             <- freshTyFun g l f =<< getDefType f
       g'             <- envAdds [(f, ft)] g 
       g''            <- envAddFun l g' f xs ft >>= envAddNil l
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
         let g''   =  envAddReturn f (F.subst su' $ b_type t') g'
         g'''      <- envAdds (envBinds su' xs ts') g''
         envAdds tyBinds g'''
  where  
    (αs, yts, h, _, t)  = mfromJust "envAddFun" $ bkFun ft
    tyBinds             = [(Loc (srcPos l) α, tVar α) | α <- αs]
    varBinds            = safeZip "envAddFun"
    envBinds su xs ts   = varBinds xs (F.subst su <$> ts)
    (su, ts')           = renameBinds yts xs
    t'                  = F.subst su <$> t

envAddNil l g = snd <$> envAddHeap l g nilHeap
    where
      nilHeap = heapAdd "envAddNil" nilLoc nilBind heapEmpty

envAddHeap l g σ
  = do xs              <- mapM (return . Id (srcPos l) . F.symbolString . b_sym) bs
       let (su, ts_pre) = renameBinds bs xs
           ts           = map (uncurry strengthenObjBinds) (zip xs ts_pre)
           σ'           = heapFromBinds "envAddHeap" (zip ls xs)
       (ts',g')        <- foldM foldFresh ([],g) ts
       let g''          = g' { rheap = heapCombine "envAddHeap" [σ', rheap g'] }
       g'''            <- envAdds (varBinds xs (reverse ts')) g''
       return (su, g''')
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

consReturnHeap :: CGEnv -> Maybe (F.Symbol, Id AnnTypeR) -> Statement AnnTypeR -> CGM (F.Subst, RSubst RReft)
consReturnHeap g xro (ReturnStmt l _)
  = do (_,σ)         <- (apply θi <$>) <$> getFunHeaps g l
       let rsu       = F.mkSubst $ maybe [] (\(b,x) -> [(b, F.eVar $ F.symbol x)]) xro
       let (su,σ')   = fmap b_type <$> renameHeapBinds (rheap g) (fmap (F.subst rsu <$>) σ)
       let g'        = g { renv = envMap (F.subst su <$>) $ renv g }
       -- "Relax" subtyping checks on *new* locations in the output heap
       -- for all x with l \in locs(x), add x:<l> <: z:T, then do
       -- subtyping under G;x:T. (If all refs are _|_ then z:_|_)
       subTypeHeaps l g' (flip envFindTy g' <$> rheap g')
                         (fmap (F.subst su) <$> σ')
       return (rsu `F.catSubst` su, θi)
    where
      θi = head $ [ fromLists [] ls | WorldInst ls <- ann_fact l ] :: RSubst RReft

consReturnHeap _ _ _ = undefined           

getFunHeaps g _
  = (fromJust . funHeaps . flip envFindTy g) <$> getFun

getFunRetBinder g _
  = (retBind . fromJust . bkFun . flip envFindTy g) <$> getFun
  where
    retBind (_,_,_,_,b) = b_sym $ b


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
consAccess l x g i = do [(_,t)]          <- dotAccessM l g i $ envFindTy x g
                        envAddFresh l t g
              
dotAccessM l g f u@(TApp TUn _ _ _)
  = do concat <$> mapM dotAccessStrongEnv ts'
  where (TApp TUn ts' _ _)     = strengthenUnion u 
        dotAccessStrongEnv t = do (_, g') <- envAddFresh l t g 
                                  dotAccessM l g' f t


dotAccessM _ g f t@(TApp (TRef l) _ _ _)
  = do γ <- getTDefs
       let results = fromJust $ dotAccessRef (γ, flip envFindTy g <$> rheap g) f t
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

consCall g l _ es ft 
  = do (_,its,hi',ho',ot) <- mfromJust "consCall" . bkFun <$> instantiate l g ft
       (xes, g')          <- consScan consExpr g es
       let (argSu, ts')   = renameBinds its xes
           (heapSu, hi'') = fmap b_type <$> renameHeapBinds (rheap g') hi'
           su             = heapSu `F.catSubst` argSu
           σin            = flip envFindTy g' <$> rheap g'
       -- Substitute binders in spec with binders in actual heap
       zipWithM_ (withAlignedM $ subTypeContainers l g') [envFindTy x g' | x <- xes] (F.subst su ts')
       subTypeHeaps l g' σin (F.subst su <$> hi'')
       let hu             = foldl (flip heapDel) (rheap g') $ heapLocs hi''
       (_,g'')           <- envAddHeap l (g' { rheap = hu }) (fmap (F.subst su) <$> ho')
       let lost  = deletedLocs σin $ rheap g''
           B rs rt = fmap (F.subst su) ot
           g'''  = g'' { renv  = envMap (deleteLocsTy lost) $ renv g''
                       , rheap = heapFromBinds "consCall" . filter ((`notElem` lost) . fst) . heapBinds . rheap $ g''
                       }
       g_out             <- topMissingBinds g''' (rheap g') hi' >>= envAdds [(rs, rt)]
       return (Id l $ F.symbolString rs, g_out)
                                        
     {- where
         msg xes its = printf "consCall-SUBST %s %s" (ppshow xes) (ppshow its)-}

deletedLocs σi σo = filter (`notElem` heapLocs σo) $ heapLocs σi         

topMissingBinds g σ σenv
  = envAdds (zip bs $ repeat tTop) g
    where ls = filter (`notElem` heapLocs σ) $ heapLocs σenv
          bs = map (b_sym . rd) ls
          rd l = heapRead "topMissingBinds" l σenv

instantiate :: AnnTypeR -> CGEnv -> RefType -> CGM RefType
instantiate l g t 
  = freshTyInst l g αs τs $ apply θl tbody
  where 
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
    let tptr     = TApp (TRef loc) [] [] F.top
    (x, g2)     <- envFreshHeapBind l loc g1
    -- pxsm        <- mapM (addMeasuresM g1) pxs
    let tob_pre  = TObj pxs F.top    
    -- This creates binders in the envt for each field
    (tob, g3)   <- freshObjBinds l g2 (x `strengthenObjBinds` tob_pre)
    g4          <- envAdds [(x,tob)] g3
    (i, g5)     <- envAddFresh l tptr g4
    return       $ {- trace (printf "Adding: %s :: %s" (ppshow i) (ppshow tob)) -} (i,g5)
  where          
    loc = head [ l | LocInst l <- ann_fact l]
    
---------------------------------------------------------------------------------
consWind :: AnnTypeR -> CGEnv -> (Location, [Location], Id SourceSpan, RSubst RReft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consWind l g (m, wls, ty, θ)
  -- What needs to be done here:
  -- Given the instantiation θ:
  -- Instantiate C[α] and add a new binder. oh wait, that is fairly easy...
  = do (σenv, (_,tw), t, ms) <- freshConsWind g l θ ty m
       let xts               = toIdTyPair <$> heapTypes σenv
           σw                = toId <$> σenv
           g'                = g { rheap =  heapDiff (rheap g) (m:wls) }
           r                 = instMeasures [F.vv Nothing] ms
       g_st                 <- envAdds xts g
       subTypeWind l g_st σw (snd $ hpRead g_st (rheap g_st) m) tw
       (z, g'')             <- envFreshHeapBind l m g'
       -- g''                  <- envAdds xts g''
       g''' <- envAdds [(z, strengthen t r)]  g''
       applyLocMeasEnv m g'''
       where
         hpRead        = safeRefReadHeap "consWind"
         s             = srcPos l
         toId          = Id s . F.symbolString . b_sym                      
         toIdTyPair b  = (toId b, b_type b)
         heapDiff σ ls = foldl (flip heapDel) σ ls

freshConsWind g l θ ty m
    = do (σenv, (x,tw), t, ms) <- freshTyWind g l θ ty
         let xsu         = F.mkSubst [(x, F.eVar x')]
             (hsu,σenv') = renameHeapBinds (rheap g) σenv
             su          = F.catSubst xsu hsu
             σenv''      = fmap (F.subst su) <$> σenv'
             t'          = F.subst su t
             ms'         = subMeas su <$> ms 
         return (σenv'', (x',tw), t', ms')
    where
      x'                  = hpRead m (rheap g)
      subMeas su (f,as,e) = (f, as, F.subst su e)
      hpRead              = heapRead "freshConsWind"

                            


---------------------------------------------------------------------------------
consUnwind :: AnnTypeR -> CGEnv -> (Location, Id SourceSpan, RSubst RReft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consUnwind l g (m, ty, θl) =
  do 
    (σ,s,t,αs)  <- envFindTyDef ty
    (σ',t',hsu) <- unwindInst l (unwindTyApp l g m αs) θl (σ,t)
    ms          <- getRMeasures ty
    (s',g')     <- envFreshHeapBind l m g
    let r       = instRMeas su b ms
        σ''     = (instPropBind r . subst su) <$> σ'
        su      = hsu `F.catSubst` sub1 s s'
    (_, g'')    <- envAddHeap l g' σ''
    g'''        <- envAdds [(s', strengthenObjBinds s' t')] g''
    applyLocMeasEnv m g'''
  where
    subst su = fmap $ F.subst su
    sub1 x y = F.mkSubst [(F.symbol x, F.eVar y)]
    b        = F.symbol $ heapRead "consUnwind" m $ rheap g
  
instPropBind r (B x t) = B x $ strengthen t r

instRMeas su b' ms 
  = F.subst su $ instMeasures [b'] ms

unwindTyApp l g m αs
  = flip fromLists [] $ zip αs vs
    where
      -- msg   = "%s BUG: unwound something bad! %s"
      err p = error $ printf (ppshow (srcPos l)) (ppshow p)
      vs    = case safeRefReadHeap "consUnwind" g (rheap g) m of
                (_,TApp _ vs _ _)  -> vs
                p                  -> err p

unwindInst l θα θl (σ,t)
  = do (su, σ'') <- freshHeapEnv l σ'
       return (σ'', t', su)
  where 
    θ     = θl <> θα
    σ'    = apply θ σ
    t'    = apply θ t

consRename _ _ _
  = error "consRename"

applyLocMeasEnv l g
    = do xts' <- mapM (fmap debind . addMeasuresM g) xts
         envAdds xts' g
    where
      debind (B x t) = (x, t)
      xts    = [ B (F.symbol x) t | (x, t) <- e, l `elem` locs t ]
      e      = envToList g
