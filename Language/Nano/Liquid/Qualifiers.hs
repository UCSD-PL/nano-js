module Language.Nano.Liquid.Qualifiers (inferQuals, inferQualsFromSpec, inferQualsFromTypes) where

import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Misc
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Liquid.Types
import           Language.Nano.Types
import qualified Data.HashMap.Strict            as M
import           Language.Nano.Env
import           Language.Nano.Errors
import           Language.ECMAScript3.PrettyPrint
import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Parser.Type
import           Data.Maybe
import            Data.List
  
inferQualsFromSpec :: Nano AnnTypeR RefType -> Nano AnnTypeR RefType
inferQualsFromSpec pgm@(Nano { defs = d }) = pgm { quals = quals pgm ++ qs }
  where qs = qualifiers d
             
inferQualsFromTypes :: F.SEnv (F.SortedReft) -> Nano AnnTypeR RefType -> Nano AnnTypeR RefType
inferQualsFromTypes g pgm@(Nano { tRMeas = tm, tMeas = m, tDefs = td, consts = c }) =
  pgm { quals = quals pgm ++ qualsOfTyMeasures g td tm c }
               
qualsOfTyMeasures g td m c = concatMap (qualsOfMeasures g td c) $ M.toList m 

-- qualsOfMeasures :: F.SEnv (F.SortedReft) -> Env RefType -> (F.Symbol, [Measure]) -> [F.Qualifier]       
qualsOfMeasures g td cenv (f, ms) = map (qualOfMeasure g' cenv) ms 
  where g' = foldl' (flip $ uncurry F.insertSEnv) g [ (x, rTypeSortedReft t) | (B x t) <- heapTypes h ]
        (TBd (TD {td_heap = h})) = fromMaybe (error "qualsOfMeasures") $ envFindTy f td
                               
qualOfMeasure :: F.SEnv (F.SortedReft) -> Env RefType -> Measure -> F.Qualifier
qualOfMeasure g cenv (k, [x], e) = F.Q "AutoMeasure" ((vv,vvso):qargs) (F.subst sub p)
  where
    p = F.PAtom F.Eq lhs rhs
    -- Wow...
    lhs = F.EApp (F.Loc F.dummyPos (F.suffixSymbol k "p")) [F.eVar vv, F.eVar x]
    vv  = F.symbol "v"
    vvso = refSort
    (fs, rhs) = removeApps e
    varsorts  = catMaybes $ map (maybeSort g) $ F.syms rhs
    vsorts  = [(v, t) | (v, t) <- map (\(f, newv) -> (newv, goSort f g)) fs ]
    ivsorts = zipWith (\(v,t) i -> ("~A"++show i, v, t)) (nub $ (x,tdefSort):vsorts ++ varsorts) [0..]
    qargs    = [ (F.symbol i, t) | (i, _, t) <- ivsorts ]
    sub     = F.mkSubst ([ (v, F.eVar i) | (i, v, _) <- ivsorts])
              
maybeSort g l = F.lookupSEnv l g >>= \r -> return (l, F.sr_sort r)
            
goSort :: F.Symbol -> F.SEnv F.SortedReft -> F.Sort
goSort f g = last xs
  where
    F.RR (F.FFunc _ xs) _ = fromMaybe (error "goSort") $ F.lookupSEnv f g
    -- (_, _, [B x xt], _, _, rt)  = fromMaybe (error "qualOfMeasure") $ (envFindTy k cenv >>= bkFun)
    -- yts = zip args (fmap (rTypeSort . b_type) xts)
    -- F.RR so (F.Reft (v, _))  = rTypeSortedReft (b_type (head xts))
                  
removeApps (F.EBin b e1 e2) = (vs1 ++ vs2, F.EBin b e1' e2')
  where (vs1, e1') = removeApps e1
        (vs2, e2') = removeApps e2
removeApps (F.EIte p e1 e2) = (vs1 ++ vs2, F.EIte p e1' e2')
  where (vs1, e1') = removeApps e1
        (vs2, e2') = removeApps e2
removeApps (F.ECst e t)     = (vs, F.ECst e' t)
  where (vs, e')   = removeApps e
removeApps (F.EApp f es) 
  |  F.symbolString (F.val f) == "field_int" 
  || F.symbolString (F.val f) == "field_Ref" 
    = (vs, F.EVar s)
      where vs = [(F.val f, s)]
            s  = F.stringSymbol (foldl' (++) "" $ map F.symbolString $ (F.val f:concatMap F.syms es))
removeApps (F.EApp f es) 
    = (vs, F.EApp f es')
      where (vs, es') = foldr (\(vs, e) (vs', es') -> (vs ++ vs', e:es')) ([], []) (map removeApps es) 
removeApps e = ([], e)
                                             
qualifiers d = concatMap (refTypeQualifiers g) (envToList d)
  where 
    g :: F.SEnv F.Sort
    g = envSEnv $ envMap rTypeSort d

refTypeQualifiers :: F.SEnv F.Sort -> (Id SourceSpan, RefType) -> [F.Qualifier]
refTypeQualifiers γ0 (l, t) = efoldRType rTypeSort addQs γ0 [] t 
  where
    addQs γ t qs  = mkQuals l γ t ++ qs

mkQuals l γ t     = [ mkQual l γ v so pa | let (F.RR so (F.Reft (v, ras))) = rTypeSortedReft t 
                                         , F.RConc p                      <- ras                 
                                         , pa                             <- atoms p
                    ]

mkQual l γ v so p = F.Q "Auto" ((v, so) : yts) (F.subst θ p) 
  where 
    yts           = [(y, lookupSort l x γ) | (x, y) <- xys ]
    θ             = F.mkSubst [(x, F.eVar y)   | (x, y) <- xys]
    xys           = zipWith (\x i -> (x, F.symbol ("~A" ++ show i))) xs [0..] 
    xs            = delete v $ orderedFreeVars γ p

lookupSort l  x γ = fromMaybe err $ F.lookupSEnv x γ 
  where 
    err           = error ("Unbound variable " ++ show x ++ " in specification" ++ show (unId l))

orderedFreeVars γ = nub . filter (`F.memberSEnv` γ) . F.syms 

atoms (F.PAnd ps)   = concatMap atoms ps
atoms p           = [p]
  
inferQuals :: F.FInfo a -> F.FInfo a
inferQuals fi = fi { F.quals = qs ++ F.quals fi }
  where
    map2cs = map snd . M.toList
    qs     = inferQualsFromCs . map2cs $ F.cm fi
             
inferQualsFromCs :: [F.SubC a] -> [F.Qualifier]
inferQualsFromCs = nub . concatMap inferQualsFromC
                   
inferQualsFromC s 
  = map qualFromSubPred [ (vsu,p) | vsu <- lhsKs, p <- rhsCs ]
  where
    F.RR t (F.Reft (_,lhs)) = F.slhs s
    F.Reft (vv,rhs) = F.sr_reft $ F.srhs s
    lhsKs        = [ (vv,t,su) | F.RKvar _ su <- lhs ]
    rhsCs        = [ p         | F.RConc p    <- rhs ]

qualFromSubPred ((vv,t,su), p)
  = F.Q { F.q_name   = "AutoGenLOL"
        , F.q_params = [(vv,t)]
        , F.q_body   = F.subst su' p
      }
  where
    su'   = F.mkSubst [ (F.subst su x, F.eVar x) | x <- dom, F.subst su x /= vv ]
    dom   = F.substDom su
    psyms = F.syms p
