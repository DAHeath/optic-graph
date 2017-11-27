{-# LANGUAGE TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , MultiParamTypeClasses
           , RankNTypes
           #-}

module Data.Optic.Graph.Graph
  ( module Data.Optic.Directed.Abstract
  , reverse
  , edgesFrom, iedgesFrom
  ) where

import qualified Data.Optic.Directed.Abstract as A
import           Data.Optic.Directed.Abstract hiding (Graph)
import           Control.Lens
import           Control.Monad.State

import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Maybe (mapMaybe)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Prelude as P hiding (reverse)

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

type Graph i e v = A.Graph Identity i e v

-- | Reverse the direction of all edges in the graph.
reverse :: Ord i => Graph i e v -> Graph i e v
reverse g = foldr (\((i1, i2), e) -> addEdge i2 i1 e) onlyVerts (g ^@.. iallEdges)
  where onlyVerts = g & edgeMap .~ M.empty

instance Ord i => Reversing (Graph i e v) where
  reversing = reverse

-- | A traversal which selects all edges that originate at an index.
edgesFrom :: Ord i => i -> Traversal' (Graph i e v) e
edgesFrom i = edgeMap . ix i . traverse

-- | Indexed traversal of the edges from the given index, labelled with the
-- target index.
iedgesFrom :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesFrom i = edgeMap . ix i . itraverse . indexed

-- | All connections in the graph with both indices, vertex labels, and the edge label.
connections :: Ord i => Graph i e v -> [((i, v), e, (i, v))]
connections g =
  let es = g ^@.. iallEdges
  in mapMaybe (\((i1, i2), e) -> do
    v1 <- g ^? ix i1
    v2 <- g ^? ix i2
    return ((i1, v1), e, (i2, v2))) es

