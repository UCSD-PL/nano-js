-- | Heap definitions for Refinement Type Checker

{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE NoMonomorphismRestriction   #-}

module Language.Nano.Typecheck.Heaps (

    Heap
  , Location
  , heapEmpty
  , heapFromBinds

  , heapRead
  , heapAdd
  , heapAddWith
  , heapUpd
  , heapDel
  , heapCombine
  , heapCombineWith

  , heapLocs
  , heapBinds
  , heapTypes
  , heapMem
  , heapSplit

  ) where

import           Control.Monad
import qualified Data.HashMap.Strict     as M
import qualified Data.HashSet            as S
import           Data.Generics                   
import           Data.Maybe                 (catMaybes, isJust, fromJust)
import           Data.Typeable              ()
import           Data.List

import           Text.Printf
import           Text.PrettyPrint.HughesPJ 

import           Language.ECMAScript3.PrettyPrint
import           Language.Nano.Errors

import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Misc

-- | Locations
type Location = String

-- | Heaps binding locations to types
newtype Heap t = H (M.HashMap Location t)
    deriving (Eq, Show, Data, Typeable, Functor)

instance (Ord t) => Ord (Heap t) where
  compare (H h1) (H h2) = M.toList h1 `compare` M.toList h2 

-- | Empty heap
heapEmpty :: Heap t
heapEmpty = H M.empty

-- | List of Bindings -> Heap
heapFromBinds :: (PP t) => [(Location, t)] -> Heap t
heapFromBinds bs = foldl (\h (l,t) -> heapAdd l t h) heapEmpty bs

-- | Add a binding to a heap
heapAdd :: (PP t) => Location -> t -> Heap t -> Heap t
heapAdd l t (H h) | not (M.member l h) = heapUpd l t (H h)
heapAdd l _ h = error "Adding duplicate location to heap"

heapUpd :: Location -> t -> Heap t -> Heap t
heapUpd l t (H h) = H $ M.insert l t h                                      

heapAddWith :: (t -> t -> t) -> Location -> t -> Heap t -> Heap t
heapAddWith f l t (H h) = H $ M.insertWith f l t h

heapDel :: Location -> Heap t -> Heap t
heapDel l (H h) = H $ M.delete l h

heapRead :: (PP t) => String -> Location -> Heap t -> t
heapRead m l (H h) = if M.member l h then
                         fromJust (M.lookup l h)
                     else
                         error $ printf "[%s] Location %s not in heap\n" m l

-- | Combine a list of heaps
heapCombine :: (PP t) => [Heap t] -> Heap t
heapCombine = heapFromBinds . join . map heapBinds 

heapCombineWith :: (t -> t -> t) -> [Heap t] -> Heap t               
heapCombineWith f hs = foldl combine heapEmpty hs
    where
      combine (H h1) (H h2) = H $ M.unionWith f h1 h2
                       
heapLocs :: Heap t -> [Location]
heapLocs (H h) = M.keys h

heapBinds :: Heap t -> [(Location, t)]
heapBinds (H h) = M.toList h

heapTypes :: Heap t -> [t]
heapTypes = map snd . heapBinds          

heapMem :: Location -> Heap t -> Bool
heapMem l (H h) = M.member l h

-- Get a list of locations:                        
--   (only in σ1, both σ1 and σ2, only in σ2)          
heapSplit :: Heap t -> Heap t -> ([Location],[Location],[Location])
heapSplit σ1 σ2           
  = (only1, nub $ both1 ++ both2, only2)
    where 
      l1s = heapLocs σ1
      l2s = heapLocs σ2
      (both1,only1) = partition (`elem` l2s) l1s
      (both2,only2) = partition (`elem` l1s) l2s

