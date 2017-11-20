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
  ( Graph(..), vertMap, edgeMap
  , allVerts, iallVerts
  , edge, edgesTo, edgesFrom, allEdges
  , iedgesTo, iedgesFrom, iallEdges
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
  , reverse
  , cartesianProduct, cartesianProductWith
  ) where

import qualified Data.Optic.Directed.Abstract as A
import           Control.Lens
import           Control.Monad.State

import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Prelude as P hiding (reverse)

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

newtype Graph i e v = Graph { _getGraph :: A.Graph Identity i e v }
  deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph
makePrisms ''Graph

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




idenMap :: Ord i => Iso (Map (Identity i) a) (Map (Identity i) b)
                        (Map i a) (Map i b)
idenMap = iso (M.mapKeys runIdentity) (M.mapKeys Identity)

deIdP :: Indexable (a, b) p => p c (f d) -> Indexed (Identity a, b) c (f d)
deIdP = Indexed . deIdP' . indexed
  where deIdP' f (Identity a, b) = f (a, b)

deId :: Indexable a p => p b (f c) -> Indexed (Identity a) b (f c)
deId = Indexed . deId' . indexed
  where deId' f (Identity a) = f a

vertMap :: Lens (Graph i e v) (Graph i e v') (Map i v) (Map i v')
vertMap = getGraph . A.vertMap

edgeMap :: Ord i => Lens (Graph i e v) (Graph i e' v)
                      (Map i (Map i e)) (Map i (Map i e'))
edgeMap = getGraph . A.edgeMap . idenMap

allVerts :: Traversal (Graph i e v) (Graph i e v') v v'
allVerts = getGraph . A.allVerts

iallVerts :: IndexedTraversal i (Graph i e v) (Graph i e v') v v'
iallVerts = getGraph . A.iallVerts

edge :: (Ord i) => i -> i -> Traversal' (Graph i e v) e
edge i i' = getGraph . A.edge (Identity i) i'

allEdges :: Traversal (Graph i e v) (Graph i e' v) e e'
allEdges = getGraph . A.allEdges

iallEdges :: IndexedTraversal (i, i) (Graph i e v) (Graph i e' v) e e'
iallEdges = getGraph . A.iallEdges . deIdP

edgesTo :: Ord i => i -> Traversal' (Graph i e v) e
edgesTo i = getGraph . A.edgesTo i

iedgesTo :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesTo i = getGraph . A.iedgesTo i . deId
idxs :: Graph i e v -> [i]
idxs = A.idxs . _getGraph

idxSet :: Graph i e v -> Set i
idxSet = A.idxSet . _getGraph

empty :: Graph i e v
empty = Graph A.empty

fromLists :: Ord i => [(i, v)] -> [(i, i, e)] -> Graph i e v
fromLists vs es =
  Graph (A.fromLists vs (map (\(i1, i2, e) -> (Identity i1, i2, e)) es))

fromListsWith :: Ord i => (e -> e -> e) -> (v -> v -> v)
              -> [(i, v)] -> [(i, i, e)] -> Graph i e v
fromListsWith fe fv vs es =
  Graph (A.fromListsWith fe fv vs (map (\(i1, i2, e) -> (Identity i1, i2, e)) es))

addEdgeWith :: Ord i => (e -> e -> e) -> i -> i -> e -> Graph i e v -> Graph i e v
addEdgeWith fe i1 i2 e = over _Graph (A.addEdgeWith fe (Identity i1) i2 e)

addEdge :: Ord i => i -> i -> e -> Graph i e v -> Graph i e v
addEdge i1 i2 e = over _Graph (A.addEdge (Identity i1) i2 e)

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
delVert v = _Graph %~ A.delVert v

delEdge :: Ord i => i -> i -> Graph i e v -> Graph i e v
delEdge i1 i2 = _Graph %~ A.delEdge (Identity i1) i2

delIdx :: Ord i => i -> Graph i e v -> Graph i e v
delIdx i = _Graph %~ A.delIdx i

filterVerts :: Ord i => (v -> Bool) -> Graph i e v -> Graph i e v
filterVerts p = _Graph %~ A.filterVerts p

ifilterVerts :: Ord i => (i -> v -> Bool) -> Graph i e v -> Graph i e v
ifilterVerts p = _Graph %~ A.ifilterVerts p

filterEdges :: Ord i => (e -> Bool) -> Graph i e v -> Graph i e v
filterEdges p = _Graph %~ A.filterEdges p

ifilterEdges :: Ord i => (i -> i -> e -> Bool) -> Graph i e v -> Graph i e v
ifilterEdges p = _Graph %~ A.ifilterEdges (\(Identity i1) -> p i1)

filterIdxs :: Ord i => (i -> Bool) -> Graph i e v -> Graph i e v
filterIdxs p = _Graph %~ A.filterIdxs p

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

mapIdx :: Ord i' => (i -> i') -> Graph i e v -> Graph i' e v
mapIdx f = _Graph %~ A.mapIdx f

travIdx :: (Applicative f, Ord i, Ord i')
        => (i -> f i') -> Graph i e v -> f (Graph i' e v)
travIdx f = _Graph %%~ A.travIdx f

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
