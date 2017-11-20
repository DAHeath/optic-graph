{-# LANGUAGE TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , MultiParamTypeClasses
           , RankNTypes
           , NoMonomorphismRestriction
           #-}

module Data.Optic.Directed.HyperGraph.Graph
  ( Graph, vertMap, edgeMap
  , allVerts, iallVerts
  , edge
  , edgesTo
  -- , edgesFrom
  , allEdges
  , iedgesTo
  -- , iedgesFrom
  , iallEdges
  , idxs, idxSet
  , empty
  , fromLists, fromListsWith
  , union, unionWith
  , addVert, addVertWith
  , addEdge, addEdgeWith
  , delVert, delEdge, delIdx
  , filterVerts, ifilterVerts
  , filterEdges, ifilterEdges
  , filterIdxs
  -- , reverse
  , cartesianProduct, cartesianProductWith
  ) where

import qualified Data.Optic.Directed.Abstract as A
import           Control.Lens

import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

newtype Graph i e v = Graph { _getGraph :: A.Graph Set i e v }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph
makePrisms ''Graph

vertMap :: Lens (Graph i e v) (Graph i e v') (Map i v) (Map i v')
vertMap = getGraph . A.vertMap

edgeMap :: Lens (Graph i e v) (Graph i e' v)
                (Map (Set i) (Map i e)) (Map (Set i) (Map i e'))
edgeMap = getGraph . A.edgeMap

allVerts :: Traversal (Graph i e v) (Graph i e v') v v'
allVerts = getGraph . A.allVerts

iallVerts :: IndexedTraversal i (Graph i e v) (Graph i e v') v v'
iallVerts = getGraph . A.iallVerts

edge :: (Ord i) => Set i -> i -> Traversal' (Graph i e v) e
edge is i = getGraph . A.edge is i

allEdges :: Traversal (Graph i e v) (Graph i e' v) e e'
allEdges = getGraph . A.allEdges

iallEdges :: IndexedTraversal (Set i, i) (Graph i e v) (Graph i e' v) e e'
iallEdges = getGraph . A.iallEdges

edgesTo :: Ord i => i -> Traversal' (Graph i e v) e
edgesTo i = getGraph . A.edgesTo i

iedgesTo :: Ord i => i -> IndexedTraversal' (Set i) (Graph i e v) e
iedgesTo i = getGraph . A.iedgesTo i

idxs :: Graph i e v -> [i]
idxs = A.idxs . _getGraph

idxSet :: Graph i e v -> Set i
idxSet = A.idxSet . _getGraph

empty :: Graph i e v
empty = Graph A.empty

fromLists :: Ord i => [(i, v)] -> [(Set i, i, e)] -> Graph i e v
fromLists vs = Graph . A.fromLists vs

fromListsWith :: Ord i => (e -> e -> e) -> (v -> v -> v)
              -> [(i, v)] -> [(Set i, i, e)] -> Graph i e v
fromListsWith fe fv vs = Graph . A.fromListsWith fe fv vs

addEdgeWith :: Ord i => (e -> e -> e) -> Set i -> i -> e -> Graph i e v -> Graph i e v
addEdgeWith fe is1 i2 e = over _Graph (A.addEdgeWith fe is1 i2 e)

addEdge :: Ord i => Set i -> i -> e -> Graph i e v -> Graph i e v
addEdge is1 i2 e = over _Graph (A.addEdge is1 i2 e)

addVert :: Ord i => i -> v -> Graph i e v -> Graph i e v
addVert i v = over _Graph (A.addVert i v)

addVertWith :: Ord i => (v -> v -> v) -> i -> v -> Graph i e v -> Graph i e v
addVertWith fv i v = over _Graph (A.addVertWith fv i v)

union :: Ord i => Graph i e v -> Graph i e v -> Graph i e v
union (Graph g1) (Graph g2) = Graph (A.union g1 g2)

unionWith :: Ord i
          => (e -> e -> e) -> (v -> v -> v)
          -> Graph i e v -> Graph i e v -> Graph i e v
unionWith fe fv (Graph g1) (Graph g2) = Graph (A.unionWith fe fv g1 g2)

delVert :: (Eq v, Ord i) => v -> Graph i e v -> Graph i e v
delVert v = over _Graph (A.delVert v)

delEdge :: Ord i => Set i -> i -> Graph i e v -> Graph i e v
delEdge i1 i2 = over _Graph (A.delEdge i1 i2)

delIdx :: Ord i => i -> Graph i e v -> Graph i e v
delIdx i = over _Graph (A.delIdx i)

filterVerts :: Ord i => (v -> Bool) -> Graph i e v -> Graph i e v
filterVerts p = over _Graph (A.filterVerts p)

ifilterVerts :: Ord i => (i -> v -> Bool) -> Graph i e v -> Graph i e v
ifilterVerts p = over _Graph (A.ifilterVerts p)

filterEdges :: Ord i => (e -> Bool) -> Graph i e v -> Graph i e v
filterEdges p = over _Graph (A.filterEdges p)

ifilterEdges :: Ord i => (Set i -> i -> e -> Bool) -> Graph i e v -> Graph i e v
ifilterEdges p = over _Graph (A.ifilterEdges p)

filterIdxs :: Ord i => (i -> Bool) -> Graph i e v -> Graph i e v
filterIdxs p = over _Graph (A.filterIdxs p)

cartesianProduct :: Ord i3
                 => (i1 -> i2 -> i3)
                 -> (v1 -> v2 -> v3)
                 -> Graph i1 e v1 -> Graph i2 e v2 -> Graph i3 e v3
cartesianProduct fi fv (Graph g1) (Graph g2) =
  Graph (A.cartesianProduct fi fv g1 g2)

cartesianProductWith :: Ord i3
                     => (e -> e -> e)
                     -> (v3 -> v3 -> v3)
                     -> (i1 -> i2 -> i3)
                     -> (v1 -> v2 -> v3)
                     -> Graph i1 e v1 -> Graph i2 e v2 -> Graph i3 e v3
cartesianProductWith fe fv fi prod (Graph g1) (Graph g2) =
  Graph (A.cartesianProductWith fe fv fi prod g1 g2)

type instance Index (Graph i e v) = i
type instance IxValue (Graph i e v) = v
instance Ord i => Ixed (Graph i e v)
instance Ord i => At (Graph i e v) where
  at i = vertMap . at i

instance Ord i => Monoid (Graph i e v) where
  mempty = empty
  mappend = union

instance Ord i => Semigroup (Graph i e v)
instance AsEmpty (Graph i e v) where
  _Empty = _Graph . _Empty

instance Functor (Graph i e) where
  fmap f = _Graph %~ fmap f

instance Foldable (Graph i e) where
  foldr f acc = foldr f acc . _getGraph

instance Traversable (Graph i e) where
  traverse f = _Graph %%~ traverse f

instance (i ~ i', e ~ e') => Each (Graph i e v) (Graph i' e' v') v v' where
  each = traversed

instance FunctorWithIndex i (Graph i e)
instance FoldableWithIndex i (Graph i e)
instance TraversableWithIndex i (Graph i e) where
  itraverse f = _Graph %%~ itraverse f

instance Bifunctor (Graph i) where
  bimap fe fv = _Graph %~ bimap fe fv

instance Bifoldable (Graph i) where
  bifoldr fe fv acc = bifoldr fe fv acc . _getGraph

instance Ord i => Bitraversable (Graph i) where
  bitraverse fe fv = _Graph %%~ bitraverse fe fv
