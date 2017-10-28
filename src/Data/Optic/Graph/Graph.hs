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
  , empty, fromLists, union, unionWith
  , addVert, addEdge
  , delVert
  , delEdgeBy, delEdge
  , delIdx
  , filterVerts, ifilterVerts
  , filterEdges, ifilterEdges
  , filterIdxs
  , reverse
  ) where

import           Control.Lens
import           Control.Monad.State

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

data Graph i e v = Graph
  { _vertMap :: Map i v
  , _edgeMap :: Map i (Map i e)
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

-- | To simplify the implementation of traversals, we record the order in which
-- the graph short be modified.
-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal (Graph i e v) (Graph i e v') v v'
allVerts = vertMap . traverse

-- | Indexed traversal of all vertices.
iallVerts :: IndexedTraversal i (Graph i e v) (Graph i e v') v v'
iallVerts = vertMap . itraverse . indexed

-- | A traversal which selects all edges between two indices.
edge :: Ord i => i -> i -> Traversal' (Graph i e v) e
edge i1 i2 = edgeMap . ix i1 . ix i2

-- | A traversal which selects all edges that originate at an index.
edgesFrom :: Ord i => i -> Traversal' (Graph i e v) e
edgesFrom i = edgeMap . ix i . traverse

-- | A traversal which selects all edges that come from a different index.
edgesTo :: Ord i => i -> Traversal' (Graph i e v) e
edgesTo = iedgesTo

-- | Indexed traversal of the edges from the given index, labelled with the
-- target index.
iedgesFrom :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesFrom i = edgeMap . ix i . itraverse . indexed

-- | Indexed traversal of the edges that come from a different index, labelled with
-- the source index.
iedgesTo :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesTo i = reversed . edgeMap . ix i . itraverse . indexed

-- | A traversal which selects all edges in the graph.
allEdges :: Traversal (Graph i e v) (Graph i e' v) e e'
allEdges = edgeMap . traverse . traverse

-- | Indexed traversal of all edges in the graph.
iallEdges :: IndexedTraversal (i, i) (Graph i e v) (Graph i e' v) e e'
iallEdges = edgeMap . map1 . indexed
  where
    map1 f = itraverse (map2 f)
    map2 f i = itraverse (\i' -> f (i, i'))

-- | Indices of the graph in ascending order.
idxs :: Graph i e v -> [i]
idxs = views vertMap M.keys

-- | The set of all indices in the graph.
idxSet :: Graph i e v -> Set i
idxSet = views vertMap M.keysSet

-- | A graph with no vertices and no edges.
empty :: Graph i e v
empty = Graph M.empty M.empty

-- | Build a graph from a list of labelled vertices and labelled edges.
fromLists :: Ord k => [(k, v)] -> [(k, k, e)] -> Graph k e v
fromLists vs = foldr (\(i1, i2, e) -> addEdge i1 i2 e) (foldr (uncurry addVert) empty vs)

-- | Combine two graphs. If both graph have a vertex/edge at the same index, use the
-- vertex label from the first graph.
union :: Ord i => Graph i e v -> Graph i e v -> Graph i e v
union = unionWith const const

-- | Combine two graphs. If both graphs have a vertex at the same index, use the
-- provided function to decide how to generate the new vertex at the index.
unionWith :: Ord i => (v -> v -> v) -> (e -> e -> e)
          -> Graph i e v -> Graph i e v -> Graph i e v
unionWith fv fe (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith fv v1 v2)
        (M.unionWith (M.unionWith fe) f1 f2)

instance Ord i => Monoid (Graph i e v) where
  mempty = empty
  mappend = union

instance Ord i => Semigroup (Graph i e v)
instance AsEmpty (Graph i e v) where
  _Empty = nearly empty (\g -> null (g ^. vertMap) && null (g ^. edgeMap))

-- | Add a vertex at the index, or replace the vertex at that index.
addVert :: Ord i => i -> v -> Graph i e v -> Graph i e v
addVert i v = at i ?~ v

-- | Add an edge between two indices in the graph if both indices have vertices. If
-- they do not, the graph is unchanged.
addEdge :: Ord i => i -> i -> e -> Graph i e v -> Graph i e v
addEdge i1 i2 e g = g &
  if has (ix i1) g && has (ix i2) g
  then edgeMap . at i1 . non' _Empty . at i2 ?~ e
  else id

-- | Delete all vertices that are equal to the given value.
-- If a vertex is removed, its index and all corresponding edges are also removed.
delVert :: (Eq v, Ord i) => v -> Graph i e v -> Graph i e v
delVert v = filterVerts (not . (==) v)

-- | Remove all edges occurring between two indices.
delEdge :: Ord i => i -> i -> Graph i e v -> Graph i e v
delEdge i1 i2 = edgeMap . at i1 . non' _Empty . at i2 .~ Nothing

-- | Delete the edge between the two indices if it satisfies the predicate.
delEdgeBy :: Ord i => i -> i -> (e -> Bool) -> Graph i e v -> Graph i e v
delEdgeBy i1 i2 p = edgeMap . at i1 . non' _Empty . at i2 %~ mfilter (not . p)

-- | Remove a index from the graph, deleting the corresponding vertices and
-- edges to and from the index.
delIdx :: Ord i => i -> Graph i e v -> Graph i e v
delIdx i g = g & vertMap %~ M.delete i
               & edgeMap %~ M.delete i
               & edgeMap %~ M.mapMaybe ((non' _Empty %~ M.delete i) . Just)

-- | Filter the vertices in the graph by the given predicate.
-- If a vertex is removed, its index and all corresponding edges are also removed.
filterVerts :: Ord i => (v -> Bool) -> Graph i e v -> Graph i e v
filterVerts p = ifilterVerts (const p)

-- | Filter the vertices in the graph by the given predicate which also takes the
-- vertex index as an argument.
-- If a vertex is removed, its index and all corresponding edges are also removed.
ifilterVerts :: Ord i => (i -> v -> Bool) -> Graph i e v -> Graph i e v
ifilterVerts p g =
  let meetsP = g & vertMap %~ M.filterWithKey p
  in foldr delIdx meetsP (idxSet g `S.difference` idxSet meetsP)

-- | Filter the edges in the graph by the given predicate.
filterEdges :: Ord i => (e -> Bool) -> Graph i e v -> Graph i e v
filterEdges p g =
  foldr (\((i1, i2), _) -> delEdgeBy i1 i2 (not . p)) g (g ^@.. iallEdges)

-- | Filter the edges in the graph by the given predicate which also takes the
-- edge indices as additional arguments.
ifilterEdges :: Ord i => (i -> i -> e -> Bool) -> Graph i e v -> Graph i e v
ifilterEdges p g =
  foldr (\((i1, i2), _) -> delEdgeBy i1 i2 (not . p i1 i2)) g (g ^@.. iallEdges)

-- | Filter the indices in the graph by the given predicate.
filterIdxs :: Ord i => (i -> Bool) -> Graph i e v -> Graph i e v
filterIdxs p g = foldr delIdx g (filter (not . p) (idxs g))

-- | Reverse the direction of all edges in the graph.
reverse :: Ord i => Graph i e v -> Graph i e v
reverse g = foldr (\((i1, i2), e) -> addEdge i2 i1 e) onlyVerts (g ^@.. iallEdges)
  where
    onlyVerts = Graph (g ^. vertMap) M.empty

instance Ord i => Reversing (Graph i e v) where
  reversing = reverse

instance Functor (Graph i e) where
  fmap = over vertMap . fmap

instance Foldable (Graph i e) where
  foldr = foldrOf (vertMap . traverse)

instance Traversable (Graph i e) where
  traverse = traverseOf (vertMap . traverse)

instance (i ~ i', e ~ e') => Each (Graph i e v) (Graph i' e' v') v v' where
  each = traversed

instance FunctorWithIndex i (Graph i e)
instance FoldableWithIndex i (Graph i e)
instance TraversableWithIndex i (Graph i e) where
  itraverse = itraverseOf (vertMap . itraverse . runIndexed)

type instance Index (Graph i e v) = i
type instance IxValue (Graph i e v) = v
instance Ord i => Ixed (Graph i e v)
instance Ord i => At (Graph i e v) where
  at i = vertMap . at i

instance Bifunctor (Graph i) where
  bimap fe fv (Graph vs es) = Graph (M.map fv vs) (M.map (M.map fe) es)

instance Bifoldable (Graph i) where
  bifoldr fe fv acc g = execState (bitraverse_ (modify . fe) (modify . fv) g) acc

instance Ord i => Bitraversable (Graph i) where
  bitraverse fe fv (Graph vs es) =
    Graph <$> traverse fv vs
          <*> traverse (traverse fe) es

instance (Ord i, Arbitrary i, Arbitrary e, Arbitrary v) => Arbitrary (Graph i e v) where
  arbitrary = do
    ks <- arbitrary
    vs <- arbVerts ks
    es <- if null ks then return [] else G.listOf (arbEdge ks)
    return (fromLists vs es)
    where
      arbVerts = traverse (\i -> (\v -> (i, v)) <$> arbitrary)
      arbEdge ks = do
        i1 <- G.elements ks
        i2 <- G.elements ks
        e <- arbitrary
        return (i1, i2, e)
  shrink = const []
