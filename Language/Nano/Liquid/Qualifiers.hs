module Language.Nano.Liquid.Qualifiers (inferQuals) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Misc
import qualified Data.HashMap.Strict            as M
import            Data.List
  
inferQuals :: FInfo a -> FInfo a
inferQuals fi = fi { quals = qs ++ quals fi }
  where
    map2cs = map snd . M.toList
    qs     = inferQualsFromCs . map2cs $ cm fi
             
inferQualsFromCs :: [SubC a] -> [Qualifier]
inferQualsFromCs = nub . concatMap inferQualsFromC
                   
inferQualsFromC s 
  = map qualFromSubPred [ (vsu,p) | vsu <- lhsKs, p <- rhsCs ]
  where
    RR t (Reft (_,lhs)) = slhs s
    Reft (vv,rhs) = sr_reft $ srhs s
    lhsKs        = [ (vv,t,su) | RKvar _ su <- lhs ]
    rhsCs        = [ p         | RConc p    <- rhs ]

qualFromSubPred ((vv,t,su), p)
  = Q { q_name   = "AutoGenLOL"
      , q_params = [(vv,t)]
      , q_body   = subst su' p
      }
  where
    su'   = mkSubst [ (subst su x, eVar x) | x <- dom, subst su x /= vv ]
    dom   = substDom su
    psyms = syms p
