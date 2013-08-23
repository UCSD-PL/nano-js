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
  , emp
  , hFromBindings

  , rdLocation
  , addLocation
  , addLocationWith
  , updLocation
  , delLocation
  , combineHeaps
  , combineHeapsWith

  , hlocs
  , hbinds
  , htypes
  , hmem

  ) where

import           Control.Monad
import qualified Data.HashMap.Strict     as M
import           Data.Generics                   
import           Data.Maybe                 (catMaybes, isJust, fromJust)
import           Data.Typeable              ()

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
emp :: Heap t
emp = H M.empty

-- | List of Bindings -> Heap
hFromBindings :: (PP t) => [(Location, t)] -> Heap t
hFromBindings bs = foldl (\h (l,t) -> addLocation l t h) emp bs

-- | Add a binding to a heap
addLocation :: (PP t) => Location -> t -> Heap t -> Heap t
addLocation l t (H h) | not (M.member l h) = updLocation l t (H h)
addLocation l _ h = error "Adding duplicate location to heap"

updLocation :: Location -> t -> Heap t -> Heap t
updLocation l t (H h) = H $ M.insert l t h                                      

addLocationWith :: (t -> t -> t) -> Location -> t -> Heap t -> Heap t
addLocationWith f l t (H h) = H $ M.insertWith f l t h

delLocation :: Location -> Heap t -> Heap t
delLocation l (H h) = H $ M.delete l h

rdLocation  :: (PP t) => Location -> Heap t -> t
rdLocation l (H h) = if M.member l h then
                         fromJust (M.lookup l h)
                     else
                         error $ printf "Location %s not in heap\n" l

-- | Combine a list of heaps
combineHeaps :: (PP t) => [Heap t] -> Heap t
combineHeaps = hFromBindings . join . map hbinds

combineHeapsWith :: (t -> t -> t) -> [Heap t] -> Heap t               
combineHeapsWith f hs = foldl (\(H h1) (H h2) -> H $ M.unionWith f h1 h2 ) emp hs

hlocs :: Heap t -> [Location]
hlocs (H h) = M.keys h

hbinds :: Heap t -> [(Location, t)]
hbinds (H h) = M.toList h

htypes :: Heap t -> [t]
htypes = map snd . hbinds          

hmem :: Location -> Heap t -> Bool
hmem l (H h) = M.member l h
