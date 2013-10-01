{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TupleSections        #-}

-- | Top Level for Refinement Type checker

module Language.Nano.Liquid.Liquid (verifyFile) where

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
import           Language.Nano.Env                  (envUnion)
import           Language.Nano.Types
import qualified Language.Nano.Annots               as A
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Typecheck.WindFuns
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
  = initCGEnv pgm `seq` 
    consStmts (initCGEnv pgm) fs >> return ()

  -- = forM_ fs . consFun =<< initCGEnv pgm
initCGEnv pgm = defs `seq` CGE defs heapEmpty F.emptyIBindEnv []
  where
    defs = envUnion (specs pgm) (generateWindFuns $ tDefs pgm)

--------------------------------------------------------------------------------
consFun :: CGEnv -> Statement (AnnType_ F.Reft) -> CGM CGEnv
--------------------------------------------------------------------------------
consFun g (FunctionStmt l f xs body) 
  = do ft             <- tracePP "fresh ft" <$> (freshTyFun g l f =<< getDefType f)
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
envAddFun l g f xs ft = envAdds tyBinds =<< envAdds (varBinds xs ts') =<< (return $ envAddReturn f t' g') 
  where  
    g'                  = g { rheap = F.subst su h }
    (αs, yts, h, h', t) = mfromJust "envAddFun" $ bkFun $ tracePP "ft" ft
    tyBinds             = [(Loc (srcPos l) α, tVar α) | α <- αs]
    varBinds            = safeZip "envAddFun"
    (su, ts')           = tracePP "renameBinds" <$> renameBinds (tracePP "yts" yts) (tracePP "xs" xs)
    t'                  = F.subst su t

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
       let σ      = rheap g
           tref   = tracePP "1" $ envFindTy x2 g4
           tsto   = tracePP "2" $ envFindTy x3 g4
           upds   = tracePP "upds" $ [(l,heapRead l σ) | l <- locs tref]
           updFun = if length upds == 1 then sUpdateField else wUpdateField
       -- upds' <-  mapM (updFun tsto (F.symbol x) <$>) upds
       -- (upds', g4) <- foldM (\(upds,g) (l,t) -> 
       (upds', g4) <- foldM (updFieldM updFun (F.symbol x) tsto) ([],g3) upds
       let σ'   = heapCombineWith const [heapFromBinds upds', σ]
       return $ Just g4 { rheap = tracePP "newHeap" $ σ' }
    where
      updFieldM updF f t (upds,g) (l,tobj) = 
        do (tobj',g') <- updF g f t tobj
           return ((l,tobj'):upds, g')

      sUpdateField g f t tobj = return $ (updateField t f tobj, g)
      wUpdateField g f t tobj = do
        let tobj'    = tracePP "tobj'" $ updateField t f $ tracePP "tobj" tobj
        (x,g')      <- subTypeWUpdate l2 g tobj tobj'
        return $ (tracePP "new type" $ envFindTy x g', g')


  -- @e3.x@ should have the exact same type with @e2@
  -- = do  (x2,g2) <- consExpr g e2
  --       (x3,g3) <- consExpr g2 e3
  --       let t2   = envFindTy x2 g2
  --           t3   = envFindTy x3 g3
  --       tx      <- dotAccessM (rheap g) x t3
  --       withAlignedM (subTypeContainers' "DotRef-assign" l2 g3) t2 tx
  --       return   $ Just g3

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
        let te    = envFindTy xe g'
            rt    = envFindReturn g'
        if isTop rt
          then withAlignedM (subTypeContainers l g') te (setRTypeR te (rTypeR rt))
          else withAlignedM (subTypeContainers' "Return" l g') te rt
        consReturnHeap g' r
        return Nothing

-- return
consStmt g r@(ReturnStmt _ Nothing)
  = consReturnHeap g r >> return Nothing 

-- function f(x1...xn){ s }
consStmt g s@(FunctionStmt _ _ _ _)
  = Just <$> consFun g s
    
consStmt g (WindAll l _)    
  = Just <$> foldM (consWind l) g ws
  where
    ws = [ (l,t,fromLists αs ls) | WindInst l t αs ls <- ann_fact l ]

consStmt g (UnwindAll l _)    
  = Just <$> foldM (consUnwind l) g ws
  where
    ws = [ (l,t,fromLists [] ls) | UnwindInst l t ls <- ann_fact l ]
    
-- OTHER (Not handled)
consStmt _ s 
  = errorstar $ "consStmt: not handled " ++ ppshow s

consReturnHeap g (ReturnStmt l _)
  = do (_,σ) <- getFunHeaps g l
       subTypeHeaps l g (tracePP "Return rheap g" (rheap g)) (tracePP "Return σ" σ)
       
getFunHeaps g l
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
       return ({- trace ("consExpr:VarRef" ++ ppshow x ++ " : " ++ ppshow t)-} x, g) 
    where 
       t   = tracePP (printf "findTy %s" (ppshow x)) $ envFindTy x g
       l   = srcPos i

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
consAccess l x g i = do locts     <- dotAccessM l g i (envFindTy x g) 
                        (xs,g')   <- foldM updLoc ([],g) locts
                        γ <- getTDefs
                        let t'   = foldl1 ((fst4.).compareTs γ) $ map (`envFindTy` g') xs
                        envAddFresh l t' g'
                        -- (x,g')  <- envAddFresh l t g
                        -- let t'   = envFindTy x g'
                        -- return (x, g' { rheap = fixHeap (rheap g') loc t' (F.symbol i) })
  where
    sy                     = F.symbol i
    fixHeap σ l tnew field = heapUpd l (updateField tnew field (heapRead l σ)) σ
    updLoc (xs,g) (m,t)    = do (x,g')  <- envAddFresh l t g
                                let t'   = envFindTy x g'
                                    g''  = g' { rheap = fixHeap (rheap g') m t' sy }
                                return  (x:xs, g'')
              
dotAccessM l g f u@(TApp TUn ts _)
  -- = do concat <$> mapM (dotAccessM l g f) ts 
  = do concat <$> mapM dotAccessStrong ts'
  where (TApp TUn ts' _) = tracePP "==>" $ strengthenUnion $ tracePP "STR" u 
        σ               = rheap g
        dotAccessStrong t = do (_, g') <- envAddFresh l t g 
                               dotAccessM l g' f t


dotAccessM _ g f t@(TApp (TRef l) _ _)
  = do γ <- getTDefs
       let results = fromJust $ dotAccessRef (γ,rheap g) f t
       return $ [(l, foldl1 ((fst4.) . compareTs γ) (map ac_result results))]

dotAccessM l g _ t = 
  tracePP "hey hey hey" () `seq`subTypeContainers' "dead access" l g tru fls >> return []
  where 
    tru = tTop
    fls = tTop `strengthen` F.predReft F.PFalse

------------------------------------------------------------------------------------------
consUpCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
------------------------------------------------------------------------------------------
consUpCast g x a e 
  = do  γ     <- getTDefs
        let b' = fst $ alignTs γ b u
        envAddFresh l b' g
  where 
    u          = rType $ head [ t | Assume t <- ann_fact a]
    b          = envFindTy x g 
    l          = getAnnotation e
      

-- No fresh K-Vars here - instead keep refs from original type
---------------------------------------------------------------------------------------------
consDownCast :: CGEnv -> Id AnnTypeR -> AnnTypeR -> Expression AnnTypeR -> CGM (Id AnnTypeR, CGEnv)
---------------------------------------------------------------------------------------------
consDownCast g x a e 
  = do  γ   <- getTDefs
        g'  <- envAdds [(x, tc)] g
        withAlignedM (subTypeContainers' "Downcast" l g) te tc
        envAddFresh l tc g'
    where 
        tc   = tracePP "tc" $ head [ t | Assume t <- ann_fact a]
        te   = tracePP "te" $ envFindTy x g
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
  = do (_,its,h,h',ot)   <- mfromJust "consCall" . bkFun <$> tracePP "ft" <$> instantiate l g ft
       (xes, g')         <- consScan consExpr g es
       let (su, ts') = tracePP "rename" <$> renameBinds (tracePP "its" its) xes
       zipWithM_ (withAlignedM $ subTypeContainers' "call" l g') (tracePP "es" [envFindTy x g' | x <- xes]) $ tracePP "ts'" ts'
       -- g'               <- stHeaps l g' h h'
       subTypeHeaps l g' (rheap g') h
       let g'' = g' { rheap = F.subst su <$> heapCombine [foldl (flip heapDel) (rheap g) $ heapLocs h, h'] }
       tracePP "output heap" (rheap g'') `seq` envAddFresh l (F.subst su ot) g''
     {- where
         msg xes its = printf "consCall-SUBST %s %s" (ppshow xes) (ppshow its)-}

     
     

instantiate :: AnnTypeR -> CGEnv -> RefType -> CGM RefType
instantiate l g t = {-  tracePP msg  <$>  -} freshTyInst l g αs τs $ tracePP "tbody" $ apply θl tbody
  where 
    (αs, tbody) = bkAll $ tracePP "t" $ t
    τs          = map snd ts
    θl          = fromLists [] ls :: RSubst F.Reft
    (ts,ls)     = tracePP "FunInst" $ head [ (ts,ls) | FunInst ts ls <- ann_fact l ]
    {-msg           = printf "instantiate [%s] %s %s" (ppshow $ ann l) (ppshow αs) (ppshow tbody)-}


getTypArgs :: AnnTypeR -> [TVar] -> [RefType] 
getTypArgs l αs
  = error "TBD: getTypArgs"
  -- = case [i | TypInst i <- ann_fact l] of 
  --     [i] | length i == length αs -> i 
  --     _                           -> errorstar $ bugMissingTypeArgs $ srcPos l

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
    (xes, g')   <- consScan consExpr g es
    let pxs      = zipWith B (map F.symbol ps) $ map (\x -> envFindTy x g') xes
    let tob      = TObj pxs F.top
    let tptr     = TApp (TRef loc) [] F.top
    (i, g'')    <- envAddFresh l tptr g'
    g'''        <- envAddsHeap l [(loc,tob)] g''
    return       $ {- trace (printf "Adding: %s :: %s" (ppshow i) (ppshow tob)) -} (i,g''')
  where          
    loc = head [ l | LocInst l <- ann_fact l]
    
---------------------------------------------------------------------------------
consWind :: AnnTypeR -> CGEnv -> (Location, Id SourceSpan, RSubst F.Reft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consWind l g (m, ty, θ) = 
  do 
    (σw, tw, t) <- freshTyWind g l (tracePP "inst" θ) ty
    subTypeWind l g (tracePP "consWind heap" σw) (heapRead m (tracePP "consWind actual heap" $ rheap g)) (tracePP "consWind type" tw)
    let ls = heapLocs $ restrictHeap [m] (rheap g)
    return $ g { rheap = heapAdd m t $ heapDiff (rheap g) ls }
    where
      heapDiff σ ls = foldl (flip heapDel) σ ls

---------------------------------------------------------------------------------
consUnwind :: AnnTypeR -> CGEnv -> (Location, Id SourceSpan, RSubst F.Reft) -> CGM (CGEnv)    
---------------------------------------------------------------------------------
consUnwind l g (m, ty, θl) =
  do 
    (σ,t,αs) <- envFindTyDef ty
    let θ = θl `mappend` fromLists (zip αs vs) []
    return $ g { rheap = tracePP "consUnwind heap" $ heapCombine [ heapUpd m (apply θ t) (rheap g)
                                     , apply θ σ
                                     ]
               }
  where 
    vs = case heapRead m (rheap g) of
           TApp _ vs _  -> vs
           _            -> error "BUG: unwound something bad!"
    
    


