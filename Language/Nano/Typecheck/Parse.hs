{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-} 
{-# LANGUAGE UndecidableInstances      #-} 
{-# LANGUAGE TypeSynonymInstances      #-} 
{-# LANGUAGE TupleSections             #-}

module Language.Nano.Typecheck.Parse (
    parseNanoFromFile 
  ) where

import           System.FilePath
import           Data.List (sort)
import           Data.Maybe (fromMaybe)
import qualified Data.HashMap.Strict            as M
import           Data.Generics.Aliases
import           Data.Generics.Schemes
import           Control.Monad
import           Text.Parsec
-- import           Text.Parsec.String hiding (Parser, parseFromFile)
import qualified Text.Parsec.Token as Token
import           Control.Applicative ((<$>), (<*), (<*>))
import           Data.Char (toLower, isLower, isSpace) 
import           Data.Monoid (mempty, mconcat, mappend)

import           Language.Fixpoint.Names (propConName)
import           Language.Fixpoint.Misc (errorstar)
import           Language.Fixpoint.Types hiding (quals, Loc)
import           Language.Fixpoint.Parse 

import           Language.Nano.Errors
import           Language.Nano.Files
import           Language.Nano.Types
import           Language.Nano.Typecheck.Types
import           Language.Nano.Typecheck.Heaps
import           Language.Nano.Liquid.Types
import           Language.Nano.Liquid.Predicates
import           Language.Nano.Env

import           Language.ECMAScript3.Syntax
import           Language.ECMAScript3.Parser        (parseJavaScriptFromFile, SourceSpan (..))

import           Language.ECMAScript3.PrettyPrint

dot        = Token.dot        lexer
--braces     = Token.braces     lexer
plus       = Token.symbol     lexer "+"
star       = Token.symbol     lexer "*"
angles     = Token.angles     lexer

----------------------------------------------------------------------------------
-- | Type Binders ----------------------------------------------------------------
----------------------------------------------------------------------------------

idBindP :: Parser (Id SourceSpan, RefType)
idBindP = xyP identifierP dcolon bareTypeP

identifierP :: Parser (Id SourceSpan)
identifierP = withSpan Id lowerIdP -- <$> getPosition <*> lowerIdP -- Lexer.identifier

tBodyP :: Parser (Id SourceSpan, RefType, [Measure])
tBodyP = do  id  <- identifierP 
             tv  <- option [] tParP
             trs <- option [] predVarDefsP
             th  <- option heapEmpty extHeapP
             ts  <- option (stringSymbol "vt") (try (symbolP >>= \b -> colon >> return b ))
             tb  <- bareTypeP
             ms  <- option [] (reserved "with" >> spaces >> typeMeasuresP)
             return $ (id, TBd $ TD (TDef id) ts tv trs th tb (idLoc id), ms)
--     foo (x) = e
-- and bar (x) = e
typeMeasuresP = do
  m  <- typeMeasureP
  spaces
  ms <- option [] $ do
                  reserved "and"
                  spaces
                  typeMeasuresP
  return $ m:ms

-- keys(x) := e         
typeMeasureP = do
  id <- symbolP
  spaces
  v  <- parens $ sepBy symbolP comma
  spaces >> reserved "=" >> spaces
  e  <- exprP
  return (id, v, e)
  
-- [A,B,C...]
tParP = brackets $ sepBy tvarP comma

withSpan f p = do pos   <- getPosition
                  x     <- p
                  pos'  <- getPosition
                  return $ f (Span pos pos') x


xyP lP sepP rP
  = (\x _ y -> (x, y)) <$> lP <*> (spaces >> sepP) <*> rP


----------------------------------------------------------------------------------
-- | RefTypes --------------------------------------------------------------------
----------------------------------------------------------------------------------

-- | Top-level parser for "bare" types. 
-- If refinements not supplied, then "top" refinement is used.

bareTypeP :: Parser RefType 
bareTypeP 
  =  try (do  ts <- bareTypeNoUnionP `sepBy1` plus
              tr <- topP   -- unions have Top ref. type atm
              case ts of
                [ ] -> error "impossible"
                [t] -> return t
                _   -> return $ TApp TUn (sort ts) [] tr)
         
 <|> try (bRefP ( do  ts <- bareTypeNoUnionP `sepBy1` plus
                      case ts of
                        [ ] -> error "impossible"
                        [_] -> error "bareTypeP parser BUG"
                        _   -> return $ TApp TUn (sort ts) [] 
                ))


bareTypeNoUnionP
  =  try bareAllP
 <|> try bareFunP
 <|>     (bareAtomP bbaseP)

-- Creating the bindings right away at bareArgP
bareFunP
  = do args   <- parens $ sepBy bareArgP comma
       h      <- (reserved "/" >> heapP) <|> return heapEmpty 
       reserved "=>" 
       ret    <- bareArgP
       h' <- do reserved "/"
                try heapP <|> (reserved "same" >> return h)
            <|> return heapEmpty 
       r      <- topP
       return $ TFun args ret h h' r

extHeapP = do reserved ("exists!")
              h <- heapP
              dot
              return h

heapP
  =  (reserved "emp" >> return heapEmpty)
 <|> do (l,t) <- heapBindP
        h     <- (try (reserved "*" >> heapP)) <|> return heapEmpty 
        return (heapAdd "heapP" l t h)

heapBindP
  = do l <- locationP
       spaces
       reserved "|->"
       spaces
       t <- bareArgP -- bareTypeP
       return (l, t)

bareArgP 
  =   (try boundTypeP)
 <|>  (argBind <$> try (bareTypeP))

boundTypeP = do s <- symbolP 
                spaces
                colon
                spaces
                B s <$> bareTypeP

argBind t = B (rTypeValueVar t) t

bareAtomP p'
  =  try (refP  p)
 <|> try (bRefP p)
--  <|> try (bindP p)   -- This case is taken separately at Function parser
 <|>     (dummyP (p <* spaces))
   where p = p' >>= \f -> return (\r -> f (ureft r))


bbaseP :: Parser (RReft -> RefType)
bbaseP 
  =  try propP -- UGH
 <|> try tvarTyP
 <|> try (TObj <$> (braces $ bindsP) )
     -- This is what allows: list [A], tree [A,B] etc...
 <|> try (TApp <$> tDefP <*> (brackets $ sepBy bareTypeP comma)) <*> predicatesP
 <|>     ((`TApp` []) <$> tconP <*> predicatesP)

propP = withSpan buildApp $ lowerWordP >>= checkProp
    where
      checkProp i | i == map toLower propConName = (i,) <$> predicatesP
      checkProp _                    = parserFail "Prop"
      buildApp s (i,ps) = (TApp (TDef (Id s propConName)) []) ps

tvarP = withSpan (\l x -> TV x l) (stringSymbol <$> upperWordP)

tvarTyP :: Parser (RReft -> RefType)
tvarTyP = do v <- tvarP
             ps <- try (angles $ sepBy monoPredicate1P comma) <|> return []
             return $ \r -> TVar v (foldl meet r (ureft <$> ps))
    


upperWordP :: Parser String
upperWordP = condIdP nice (not . isLower . head)
  where 
    nice   = ['A' .. 'Z'] ++ ['a' .. 'z'] ++ ['0'..'9']

lowerWordP :: Parser String
lowerWordP = condIdP nice (isLower . head)
  where 
    nice   = ['A' .. 'Z'] ++ ['a' .. 'z'] ++ ['0'..'9']

tconP :: Parser TCon
tconP =  try (reserved "number"    >> return TInt)
     <|> try (reserved "boolean"   >> return TBool)
     <|> try (reserved "void"      >> return TVoid)
     <|> try (reserved "top"       >> return TTop)
     <|> try (reserved "string"    >> return TString)
     <|> try (reserved "null"      >> return TNull)
     <|> try tRefP
     <|> tDefP

tRefP
  = angles $ do
      l <- locationP
      return (TRef l)

locationP = lowerIdP

tDefP 
  = do  s <- identifierP 
        -- XXX: This list will have to be enhanced.
        if unId s `elem` ["true", "false", "number", "boolean", "string", "top", "void", "null"] 
          then parserZero
          else return $ TDef s

bareAllP 
  = do reserved "forall"
       as <- many tvarP
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ substPredVarSorts $ foldr TAll (foldr TAllP t ps) as

bindsP 
  =  try (sepBy1 bareBindP comma)
 <|> (spaces >> return [])

bareBindP 
  = do  s <- binderP
        spaces      --ugly
        colon
        spaces
        t <- bareTypeP
        return $ B s t 

predVarDefsP
  =  (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP
  = withSpan mkPVar $ do
      id <- predVarIdP
      dcolon
      ts <- predVarTypeP
      return $ (id, ts)

predVarIdP = stringSymbol <$> lowerIdP             

predVarTypeP
  = do t <- bareTypeP
       let (bs, rb) = maybe err (\(_,_,bs,_,_,rb) -> (bs,rb)) $ bkFun t
       if isPropBareType (b_type rb)
          then return $ map toPairs bs
          else parserFail $ "Predicate Variable with non-Prop output type"
    where
      toPairs (B x t) = (x, toType t)
      err             = error "Expected a function (for now)"
      isPropBareType (TApp (TDef c) [] _ _) = unId c == propConName
      isPropBareType _                      = False

mkPVar l (id, xts) = PV id l τ xts'
    where
      (_,τ) = last xts
      xts'  = [ (τ, x, EVar x) | (x, τ) <- init xts ]

predicatesP
  =   try (angles $ sepBy1 predicate1P comma)
  <|> return []

monoPredicateP
  =   try (angles monoPredicate1P)
  <|> return mempty

predicate1P
  =  liftM (PMono [] . predUReft) monoPredicate1P
     <|> (braces $ liftM2 bPPoly symsP' refasP)
  where
    symsP' = do ss <- symsP
                fs <- mapM refreshSym (fst <$> ss)
                return $ zip ss fs
    refreshSym s = liftM (intSymbol (symbolString s)) freshIntP

symsP
  = do reserved "\\"
       ss <- sepBy symbolP spaces
       reserved "->"
       return $ (, TApp TUndef [] [] mempty) <$> ss
 <|> return []

bPPoly []   _    = error "Empty poly list"
bPPoly syms expr = PPoly ss var
  where
    (ss, (v,_)) = (init syms', last syms')
    syms' = [(y, s) | ((_, s), y) <- syms]
    su    = mkSubst [(x, EVar y) | ((x, _), y) <- syms]
    var   = TVar (TV dummySymbol dummySpan) (U r mempty)
    r     = su `subst` Reft (v, expr)

monoPredicate1P     
  =  try (reserved "True" >> return mempty)
 <|> try (liftM pdVar (parens predVarUseP))
 <|> liftM pdVar predVarUseP
  where
    pdVar v = Pr [fmap (const ()) v]

predVarUseP :: Parser (PVar RefType)              
predVarUseP
  = withSpan bPredUse  $ do
      p  <- predVarIdP
      xs <- try (sepBy exprP spaces) <|> return []
      return (p, xs)
    where
      bPredUse l (p, xs) = PV p l tUndef [ (tUndef, dummySymbol, x) | x <- xs ]

-- This and more lifted from LiquidHaskell
reftUReft     = (`U` mempty)
predUReft     = U dummyReft
dummyReft     = mempty
 
dummyP ::  Parser (RReft -> b) -> Parser b
dummyP fm = fm `ap` topP 

topP   :: Parser RReft
topP   = (ureft . Reft . (, []) . vv . Just) <$> freshIntP

{--- | Parses bindings of the form: `x : kind`-}
{-bindP :: Parser (Reft -> a) -> Parser a-}
{-bindP kindP-}
{-  = do v <- symbolP -}
{-       colon-}
{-       t <- kindP-}
{-       return $ t (Reft (v, []))-}

-- | Parses refined types of the form: `{ x : kind | refinement }`
bRefP :: Parser (RReft -> a) -> Parser a
bRefP kindP
  = braces $ do
      v   <- symbolP
      colon
      t   <- kindP
      spaces
      reserved "|"
      spaces
      ras <- refasP 
      return $ t (ureft $ Reft (v, ras))

-- | Parses refined types of the form: `{ kind | refinement }`
-- refP :: Parser (RReft -> a) -> Parser a
-- refP kindP
--   = braces $ do
--       t   <- kindP
--       reserved "|"
--       ras <- refasP 
--       return $ t (ureft $ Reft (stringSymbol "v", ras))

refasP :: Parser [Refa]
refasP  =  (try (brackets $ sepBy (RConc <$> predP) semi)) 
       <|> liftM ((:[]) . RConc) predP

------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

-- filePathP :: Parser FilePath
-- filePathP = angles $ many1 pathCharP
--   where pathCharP = choice $ char <$> pathChars 
--         pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']
-- 
-- 
-- embedP     = xyP upperIdP (reserved "as") fTyConP
 
binderP :: Parser Symbol
binderP = try (stringSymbol <$> idP badc)
      <|> try (star >> return (stringSymbol "*"))
      <|> liftM pwr (parens (idP bad))
      where idP p  = many1 (satisfy (not . p))
            badc c = (c == ':') ||  bad c
            bad c  = isSpace c || c `elem` "()"
            pwr s  = stringSymbol $ "(" ++ s ++ ")" 
              
-- grabs p = try (liftM2 (:) p (grabs p)) 
--        <|> return []

---------------------------------------------------------------------
------------ Interacting with Fixpoint ------------------------------
---------------------------------------------------------------------

grabUpto p  
  =  try (lookAhead p >>= return . Just)
 <|> try (eof         >> return Nothing)
 <|> (anyChar >> grabUpto p)

betweenMany leftP rightP p 
  = do z <- grabUpto leftP
       case z of
         Just _  -> liftM2 (:) (between leftP rightP p) (betweenMany leftP rightP p)
         Nothing -> return []

specWraps :: Parser a -> Parser [a] 
specWraps = betweenMany start stop
  where 
    start = string "/*@" >> spaces
    stop  = spaces >> string "*/"

---------------------------------------------------------------------------------
-- | Specifications
---------------------------------------------------------------------------------
data PSpec l t 
  = Meas (Id l, t)
  | MBody Measure
  | Bind (Id l, t) 
  | Qual Qualifier
  | Type (Id SourceSpan, t, [Measure])
  | Invt l t 
  | Include FilePath
  deriving (Show)

specP :: Parser (PSpec SourceSpan RefType)
specP 
  = try (reserved "measure"   >> measureP)
    <|> (reserved "qualif"    >> (Qual <$> qualifierP ))
    <|> (reserved "type"      >> (Type <$> tBodyP     )) 
    <|> (reserved "invariant" >> (withSpan Invt bareTypeP))
    <|> (reserved "include"   >> (Include <$> filePathP))
    <|> ({- DEFAULT -}           (Bind <$> idBindP    ))

filePathP :: Parser (FilePath)         
filePathP
    = many1 $ noneOf [' ']

measureP :: Parser (PSpec SourceSpan RefType)                     
measureP 
  = (try (Meas <$> idBindP))
    <|> (try (MBody <$> measureImpP))

measureImpP
  = do m    <- symbolP
       args <- parens $ sepBy symbolP comma
       spaces
       reserved "="
       spaces
       e  <- exprP
       return (m, args, e)

       

--------------------------------------------------------------------------------------
parseSpecFromFile :: FilePath -> IO (Nano SourceSpan RefType) 
--------------------------------------------------------------------------------------
parseSpecFromFile f = do pspecs <- parseFromFile (specWraps specP) f
                         pgms   <- mapM parseSpecFromFile (incs pspecs)
                         return (mconcat pgms `mappend` mkSpec pspecs)
    where
      dir         = takeDirectory f
      incs pspecs = [ combine dir path | Include path <- pspecs ]

-- mkSpecRec ::  (PP t, IsLocated l) => FilePath -> [PSpec l t] -> IO (Nano SourceSpan t)
-- mkSpecRec dir xs
--     = do specs <- mapM (parseSpecFromFile . combine dir) incs
--          return (mkSpec xs `mappend` (mconcat specs))
--     where

mkSpec    ::  (PP t, IsLocated l) => [PSpec l t] -> Nano a t
mkSpec xs = Nano { code   = Src [] 
                 , specs  = envFromList [b | Bind b <- xs] 
                 , defs   = envEmpty
                 , consts = envFromList [(switchProp i, t) | Meas (i, t) <- xs]
                 , tMeas  = M.fromList  [(i,(i,as,e))     | MBody (i, as, e) <- xs]
                 , tRMeas = M.fromList  [(symbol i,m) | Type (i,_,m) <- xs]
                 , tDefs  = envFromList [(i,t)        | Type (i,t,_) <- xs]
                 , quals  =             [q            | Qual q <- xs]
                 , invts  =             [Loc l' t     | Invt l t <- xs, let l' = srcPos l]
                 }

-- YUCK. Worst hack of all time.
switchProp i@(Id l x) 
  | x == (toLower <$> propConName) = Id l propConName
  | otherwise                      = i


--------------------------------------------------------------------------------------
parseCodeFromFile :: FilePath -> IO (Nano SourceSpan a) 
--------------------------------------------------------------------------------------
parseCodeFromFile = fmap mkCode . parseJavaScriptFromFile 
        
mkCode    :: [Statement SourceSpan] -> Nano SourceSpan a
mkCode ss = Nano { code   = Src (checkTopStmt <$> ss)
                 , specs  = envEmpty  
                 , defs   = envEmpty
                 , consts = envEmpty 
                 , tDefs  = envEmpty
                 , tMeas  = M.empty
                 , tRMeas  = M.empty
                 , quals  = [] 
                 , invts  = [] 
                 } 

-------------------------------------------------------------------------------
-- | Parse File and Type Signatures -------------------------------------------
-------------------------------------------------------------------------------

parseNanoFromFile :: FilePath-> IO (Nano SourceSpan RefType)
parseNanoFromFile f 
  = do code  <- parseCodeFromFile f
       spec  <- parseSpecFromFile f
       ispec <- parseSpecFromFile =<< getPreludePath
       return $ shuffleSpecDefs $ mconcat [code, spec, ispec] 

shuffleSpecDefs pgm = pgm { specs = specγ } { defs = defγ }
  where 
    defγ            = envFromList [(fn, initFunTy fn γ) | fn <- fns]
    specγ           = envFromList [(x, t) | (x, t) <- xts, not (x `envMem` defγ)]
    γ               = specs pgm
    xts             = envToList γ
    fns             = definedFuns fs 
    Src fs          = code pgm

initFunTy fn γ = fromMaybe err $ envFindTy fn γ 
  where 
    err        = errorstar $ bugUnboundVariable (srcPos fn) fn


-- SYB examples at: http://web.archive.org/web/20080622204226/http://www.cs.vu.nl/boilerplate/#suite
definedFuns       :: [Statement SourceSpan] -> [Id SourceSpan]
definedFuns stmts = everything (++) ([] `mkQ` fromFunction) stmts
  where 
    fromFunction (FunctionStmt _ x _ _) = [x] 
    fromFunction _                      = []



--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------

instance Inputable RefType where 
  rr' = doParse' bareTypeP

instance Inputable Type where 
  rr' = doParse' (fmap (const ()) <$> bareTypeP)

