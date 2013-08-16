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
  , addLocation
  , updLocation

  , hlocs
  , hbinds
  , htypes

  ) where

import qualified Data.HashMap.Strict     as M
import           Data.Generics                   
import           Data.Typeable                  ()

import           Text.Printf
import           Text.PrettyPrint.HughesPJ 

import           Language.ECMAScript3.PrettyPrint
import           Language.Nano.Errors

import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Misc


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

hlocs :: Heap t -> [Location]
hlocs (H h) = M.keys h

hbinds :: Heap t -> [(Location, t)]
hbinds (H h) = M.toList h

htypes :: Heap t -> [t]
htypes = map snd . hbinds          

              
       