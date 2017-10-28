{-# LANGUAGE TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , MultiParamTypeClasses
           , PatternSynonyms
           , ViewPatterns
           , RankNTypes
           , NoMonomorphismRestriction
           , GADTs
           , ScopedTypeVariables
           #-}

{-|
Module      : Data.Optic.Graph
Description : Directed Graphs with ordered indices.
Copyright   : (c) David Heath, 2017
              License     : BSD3
              Maintainer  : heath.davidanthony@gmail.com
              Stability   : experimental

Directed graphs with arbitrary ordered indices, edge labels, and vertex labels.
The data structure supports a number of traversals and indexed traversals for
manipulating the labels.

The module is intended to be imported qualified, in conjunction with the lens
library.
-}
module Data.Optic.Graph
  ( Graph(..), vertMap, edgeMap
  , Ctxt(..), before, here, after
  , allVerts, iallVerts
  , edgesTo, edgesFrom, allEdges
  , iedgesTo, iedgesFrom, iallEdges
  , idxs, idxSet
  , empty, fromLists, union, unionWith
  , order, size
  , elemVert, elemEdge
  , connections, successors, predecessors, ancestors, descendants
  , addVert, addEdge
  , delVert
  , delEdgeBy, delEdge
  , delIdx
  , filterVerts, ifilterVerts
  , filterEdges, ifilterEdges
  , filterIdxs
  , reverse
  , EdgeFocused(..), edgeFocused
  , mapVerts, imapVerts
  , mapEdges, imapEdges
  , mapIdxs
  , foldVerts, ifoldVerts
  , foldEdges, ifoldEdges
  , foldIdxs
  , travVerts, itravVerts
  , travEdges, itravEdges
  , travIdxs
  , reaches, reached
  , Bitraversal
  , ibitraverse
  , match, addCtxt
  , toDecomp, fromDecomp, decomp
  , scc

  , idfs, idfsVert, idfsEdge
  , idfs_, idfsVert_, idfsEdge_
  , dfs, dfsVert, dfsEdge
  , dfs_, dfsVert_, dfsEdge_, dfsIdx_

  , ibfs, ibfsVert, ibfsEdge
  , ibfs_, ibfsVert_, ibfsEdge_
  , bfs, bfsVert, bfsEdge
  , bfs_, bfsVert_, bfsEdge_, bfsIdx_

  , itop, itopVert, itopEdge
  , itop_, itopVert_, itopEdge_
  , top, topVert, topEdge
  , top_, topVert_, topEdge_, topIdx_

  , idfsFrom, idfsFromVert, idfsFromEdge
  , idfsFrom_, idfsFromVert_, idfsFromEdge_
  , dfsFrom, dfsFromVert, dfsFromEdge
  , dfsFrom_, dfsFromVert_, dfsFromEdge_, dfsFromIdx_

  , ibfsFrom, ibfsFromVert, ibfsFromEdge
  , ibfsFrom_, ibfsFromVert_, ibfsFromEdge_
  , bfsFrom, bfsFromVert, bfsFromEdge
  , bfsFrom_, bfsFromVert_, bfsFromEdge_, bfsFromIdx_

  , ipath, ipathVert, ipathEdge
  , ipath_, ipathVert_, ipathEdge_
  , path, pathVert, pathEdge
  , path_, pathVert_, pathEdge_, pathIdx_
  ) where

import           Control.Arrow
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (whileM, whileM_)

import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import           Data.List (partition, minimumBy)
import           Data.Maybe (catMaybes, mapMaybe, maybeToList)
import           Data.Bool (bool)
import           Data.Foldable (fold)

import           Prelude as P hiding (reverse)

import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as G

data Graph i e v = Graph
  { _vertMap :: Map i v
  , _edgeMap :: Map i (Map i e)
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

data Ctxt i e v = Ctxt
  { _before :: [(i, e)]
  , _here :: v
  , _after :: [(i, e)]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Ctxt

-- | To simplify the implementation of traversals, we record the order in which
-- the graph short be modified.
data Action i e v
  = Vert i v
  | Edge i i e
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Action

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

-- | The number of vertices in the graph.
order :: Integral n => Graph i e v -> n
order = toEnum . lengthOf allVerts

-- | The number of edges in the graph
size :: Integral n => Graph i e v -> n
size = toEnum . lengthOf allEdges

-- | Is there a vertex at the index?
elemVert :: Ord i => i -> Graph i e v -> Bool
elemVert i g = not $ null (g ^? vertMap .ix i)

-- | Is there an edge between the given indices?
elemEdge :: Ord i => i -> i -> Graph i e v -> Bool
elemEdge i1 i2 g = not $ null (g ^? edgeMap . ix i1 . ix i2)

-- | All connections in the graph with both indices, vertex labels, and the edge label.
connections :: Ord i => Graph i e v -> [((i, v), e, (i, v))]
connections g =
  let es = g ^@.. iallEdges
  in mapMaybe (\((i1, i2), e) -> do
    v1 <- g ^? ix i1
    v2 <- g ^? ix i2
    return ((i1, v1), e, (i2, v2))) es

-- | The successor indices for the given index.
successors :: Ord i => i -> Graph i e v -> [i]
successors i = toListOf $ iedgesFrom i . asIndex

-- | The predecessor indices for the given index.
predecessors :: Ord i => i -> Graph i e v -> [i]
predecessors i = toListOf $ reversed . iedgesFrom i . asIndex

descendants :: Ord i => Graph i e v -> i -> [i]
descendants g i = filter (/= i) $ idxs (reached i g)

ancestors :: Ord i => Graph i e v -> i -> [i]
ancestors g i = filter (/= i) $ idxs (reaches i g)

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
  let filtered = g & vertMap %~ M.filterWithKey p
  in foldr delIdx filtered (idxSet g `S.difference` idxSet filtered)

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
reverse g = foldr (\((i1, i2), e) -> addEdge i2 i1 e) init (g ^@.. iallEdges)
  where
    init = Graph (g ^. vertMap) M.empty

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

-- | By default, graphs are "focused" on the vertices, meaning that common
-- typeclass instances act on the vertices. EdgeFocused provides an alternative
-- representation where the edges are the focus of the typeclasses.
newtype EdgeFocused i v e = EdgeFocused { getEdgeFocused :: Graph i e v }
  deriving (Show, Read, Eq, Ord, Data)

-- | Isomorphism between the graph and its edge focused equivalent.
edgeFocused :: Iso (Graph i e v) (Graph i' e' v')
                   (EdgeFocused i v e) (EdgeFocused i' v' e')
edgeFocused = iso EdgeFocused getEdgeFocused

instance Functor (EdgeFocused i v) where
  fmap = over (from edgeFocused . edgeMap) . fmap . fmap

instance Foldable (EdgeFocused i v) where
  foldr = foldrOf (from edgeFocused . allEdges)

instance Traversable (EdgeFocused i v) where
  traverse = traverseOf (from edgeFocused . allEdges)

instance (i ~ i', v ~ v') => Each (EdgeFocused i v e) (EdgeFocused i' v' e') e e' where
  each = traversed

instance FunctorWithIndex (i, i) (EdgeFocused i v)
instance FoldableWithIndex (i, i) (EdgeFocused i v)
instance TraversableWithIndex (i, i) (EdgeFocused i v) where
  itraverse = itraverseOf (from edgeFocused . edgeMap . itraverse . mapT)
    where
      mapT :: Applicative f => Indexed (i, i) e (f e') -> i -> Map i e -> f (Map i e')
      mapT ix i1 = M.traverseWithKey (\i2 -> runIndexed ix (i1, i2))

-- | Apply the given function to all vertices.
mapVerts :: (v -> v') -> Graph i e v -> Graph i e v'
mapVerts = fmap

-- | Apply the given function to all vertices, taking each vertex's index as an
-- additional argument.
imapVerts :: (i -> v -> v') -> Graph i e v -> Graph i e v'
imapVerts = imap

-- | Apply the given function to all edges.
mapEdges :: (e -> e') -> Graph i e v -> Graph i e' v
mapEdges = under (from edgeFocused) . fmap

-- | Apply the given function to all edges, taking each edge's indices as
-- additional arguments.
imapEdges :: (i -> i -> e -> e') -> Graph i e v -> Graph i e' v
imapEdges = under (from edgeFocused) . imap . uncurry

-- | The map obtained by applying f to each index of s.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
mapIdxs :: Ord i' => (i -> i') -> Graph i e v -> Graph i' e v
mapIdxs f (Graph vs es) =
  Graph (M.mapKeys f vs)
        (M.mapKeys f $ fmap (M.mapKeys f) es)

-- | Aggregate the vertices.
foldVerts :: (v -> b -> b) -> b -> Graph i e v -> b
foldVerts = foldr

-- | Aggregate the vertices with the vertex index as an additional argument.
ifoldVerts :: (i -> v -> b -> b) -> b -> Graph i e v -> b
ifoldVerts = ifoldr

-- | Aggregate the edges.
foldEdges :: (e -> b -> b) -> b -> Graph i e v -> b
foldEdges f acc g = foldr f acc (EdgeFocused g)

-- | Aggregate the edges with the edge indices as additional arguments.
ifoldEdges :: (i -> i -> e -> b -> b) -> b -> Graph i e v -> b
ifoldEdges f acc g = ifoldr (uncurry f) acc (EdgeFocused g)

-- | Aggregate the indices.
foldIdxs :: (i -> b -> b) -> b -> Graph i e v -> b
foldIdxs f acc g = foldr f acc (idxs g)

-- | Traverse the vertices.
travVerts :: Applicative f => (v -> f v') -> Graph i e v -> f (Graph i e v')
travVerts = traverse

-- | Indexed vertex traversal.
itravVerts :: Applicative f => (i -> v -> f v') -> Graph i e v -> f (Graph i e v')
itravVerts = itraverse

-- | Traverse the edges.
travEdges :: Applicative f => (e -> f e') -> Graph i e v -> f (Graph i e' v)
travEdges = allEdges

-- | Indexed edge traversal.
itravEdges :: Applicative f => (i -> i -> e -> f e') -> Graph i e v -> f (Graph i e' v)
itravEdges f g = getEdgeFocused <$> itraverse (uncurry f) (EdgeFocused g)

-- | Traverse the indices.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
travIdxs :: (Applicative f, Ord i, Ord i') => (i -> f i') -> Graph i e v -> f (Graph i' e v)
travIdxs f g =
  replace (idxs g) <$> traverse f (idxs g)
  where
    replace is is' =
      let m = M.fromList (zip is is')
      in mapIdxs (\i -> m M.! i) g

instance Bifunctor (Graph i) where
  bimap fe fv = mapVerts fv . mapEdges fe

instance Bifoldable (Graph i) where
  bifoldr fe fv acc g = execState (bitraverse_ (modify . fe) (modify . fv) g) acc

instance Ord i => Bitraversable (Graph i) where
  bitraverse = dfs

type Bitraversal s t a b c d =
  forall f. Applicative f => (a -> f b) -> (c -> f d) -> s -> f t

-- | The subgraph reached from the given index.
reached :: Ord i => i -> Graph i e v -> Graph i e v
reached i = runIdentity . travActs (\_ _ e -> Identity e) (\_ v -> Identity v) (dfsFrom' i)

-- | The subgraph that reaches the given index.
reaches :: Ord i => i -> Graph i e v -> Graph i e v
reaches i = reverse . reached i . reverse

-- | Depth first and breadth first indexed bitraversals of the graph.
idfs, ibfs, ibitraverse :: (Applicative f, Ord i)
                        => (i -> i -> e -> f e')
                        -> (i -> v -> f v')
                        -> Graph i e v -> f (Graph i e' v')
idfs fe fv = travActs fe fv dfs'
ibfs fe fv = travActs fe fv bfs'
ibitraverse = idfs

-- | Topological indexed bitraversal of the graph. If the graph contains cycles,
-- returns Nothing.
itop :: (Applicative f, Ord i)
     => (i -> i -> e -> f e')
     -> (i -> v -> f v')
     -> Graph i e v -> Maybe (f (Graph i e' v'))
itop fe fv g = actionsToGraph fe fv <$> evalStateT top' (S.empty, g)

-- | Perform a depth first/breadth first indexed bitraversal of the subgraph
-- reachable from the index. Note that these are not law abiding traversals unless
-- the choice of index has a source vertex.
idfsFrom, ibfsFrom :: (Applicative f, Ord i)
           => i
           -> (i -> i -> e -> f e)
           -> (i -> v -> f v)
           -> Graph i e v -> f (Graph i e v)
idfsFrom i fe fv g =
  let g' = travActs fe fv (dfsFrom' i) g
  in delEdgeMerge <$> g' <*> pure g
ibfsFrom i fe fv g =
  let g' = travActs fe fv (bfsFrom' i) g
  in delEdgeMerge <$> g' <*> pure g

delEdgeMerge :: Ord i => Graph i e v -> Graph i e v -> Graph i e v
delEdgeMerge g' g =
  let es = g' ^@.. iallEdges
      g'' = foldr (\((i1, i2), e) -> delEdge i1 i2) g es
  in g' `union` g''

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the graph.
dfs', bfs' :: Ord i => Graph i e v -> State (Set i) [Action i e v]
dfs' = promoteFrom dfsFrom'
bfs' = promoteFrom bfsFrom'

-- | Stateful computation which calculates the topological traversal of the graph.
-- This is an implementation of Kahn's algorithm.
top' :: Ord i => StateT (Set i, Graph i e v) Maybe [Action i e v]
top' = do
  set <~ uses graph noIncoming
  acs <- fmap concat $ whileM (uses set $ not . null) $ do
    i <- zoom set $ state S.deleteFindMin
    g <- use graph
    v <- lift $ g ^. at i
    fmap (Vert i v:) $ forM (g ^@.. iedgesFrom i) $ \(i', e) -> do
      g <- graph <%= delEdge i i'
      when (hasn't (edgesTo i') g) (set %= S.insert i')
      return $ Edge i i' e
  guard =<< uses graph (nullOf allEdges)
  return acs
  where
    hasIncoming g = S.fromList $ map (snd . fst) $ g ^@.. iallEdges
    noIncoming g = idxSet g `S.difference` hasIncoming g
    set = _1
    graph = _2

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the subgraph reached from a
-- particular index.
dfsFrom', bfsFrom' :: Ord i => i -> Graph i e v -> State (Set i) [Action i e v]
dfsFrom' i g = do
  b <- contains i <<.= True
  fmap fold $ forM (guard (not b) >> g ^? ix i) $ \v ->
    fmap ((Vert i v:) . concat) $ forM (g ^@.. iedgesFrom i) $ \(i', e) ->
      (Edge i i' e:) <$> dfsFrom' i' g
bfsFrom' start g = evalStateT ((++) <$> visit start <*> loop) Seq.empty
  where
    loop =
      fmap fold $ whileM (gets $ not . null) $ do
        i <- state (\(Seq.viewl -> h Seq.:< t) -> (h, t))
        fmap fold $ forM (g ^@.. iedgesFrom i) $ \(i', e) ->
          (Edge i i' e:) <$> visit i'
    visit i = do
      b <- lift (use $ contains i)
      fmap maybeToList $ forM (guard (not b) >> g ^? ix i) $ \v -> do
        lift (contains i .= True)
        modify (Seq.|> i)
        return $ Vert i v

-- | Indexed bitraversal of a path between the two given indices (if one exists).
ipath :: (Applicative f, Ord i) => i -> i
     -> (i -> i -> e -> f e)
     -> (i -> v -> f v)
     -> Graph i e v -> Maybe (f (Graph i e v))
ipath i1 i2 fe fv g = do
  m <- dijkstra' (const 1) i1 g
  acs <- recAcs m i2
  let g' = actionsToGraph fe fv acs
  return (delEdgeMerge <$> g' <*> pure g)
  where
    recAcs m i =
      if i == i1 then (\v -> [Vert i v]) <$> g ^. at i
      else do
        (i', e, v) <- M.lookup i m
        acs <- recAcs m i'
        return (Vert i v : Edge i' i e : acs)

-- | Bellman Ford shortest path from the given index. The result is a map of
-- the index to the information required to reconstruct the path the index's
-- predecessor to the index (specifically the incoming edge and the index's
-- vertex).
dijkstra', bellmanFord' :: (Ord i, Ord n, Num n) => (e -> n) -> i -> Graph i e v
                         -> Maybe (Map i (i, e, v))
dijkstra' weight i g = fmap (view _1) $ (`execStateT` (M.empty, M.empty, idxSet g)) $ do
  dists . at i ?= 0
  whileM_ (uses iSet $ not . null) $ do
    ds <- use dists
    near <- minimumBy (\i1 i2 -> cmp (M.lookup i1 ds) (M.lookup i2 ds)) . S.toList <$> use iSet
    iSet %= S.delete near
    forM_ (g ^@.. iedgesFrom near) $ \(i', e) -> do
      ds <- use dists
      let alt = (+ weight e) <$> M.lookup near ds
      when (cmp alt (M.lookup i' ds) == LT) $ do
        v <- lift $ g ^. at i'
        dists . at i' .= alt
        actsTo . at i' ?= (near, e, v)
  where
    actsTo = _1
    dists = _2
    iSet = _3
    cmp md1 md2 = maybe GT (\d1 -> maybe LT (compare d1) md2) md1

bellmanFord' weight i g = fmap fst $ (`execStateT` (M.empty, M.empty)) $ do
  dists . at i ?= 0
  forOf_ allVerts g $ \_ ->
    iterEdgeWeights $ \i1 i2 e d -> do
      v <- lift $ g ^. at i2
      dists . at i2 ?= d
      actsTo . at i2 ?= (i1, e, v)
  iterEdgeWeights (\_ _ _ _ -> mzero)
  where
    -- call the action when a lower weight path is found
    iterEdgeWeights ac =
      iforOf_ iallEdges g $ \(i1, i2) e -> do
        let w = weight e
        md1 <- use (dists . at i1)
        md2 <- use (dists . at i2)
        forM_ (cmp md1 w md2) (ac i1 i2 e)

    -- d1 + w < d2? Nothing represents infinite weight.
    cmp md1 w md2 = do
      d1 <- md1
      case md2 of
        Nothing -> Just (d1 + w)
        Just d2 -> if d1 + w < d2 then Just (d1 + w) else Nothing
    actsTo = _1
    dists = _2

-- | Promote a partial traversal (which only reaches a portion of the graph) to
-- a full traversal by repeatedly invoking the partial traversal on non-visited
-- indices.
promoteFrom :: Ord i
            => (i -> Graph i e v -> State (Set i) [Action i e v])
            -> Graph i e v -> State (Set i) [Action i e v]
promoteFrom fr g = do
  s <- gets $ S.difference $ idxSet g
  if null s
    then return []
    else (++) <$> fr (S.findMin s) g <*> promoteFrom fr g

-- | Promote a stateful generator of graph actions to a indexed bitraversal.
travActs :: (Ord i, Applicative f)
         => (i -> i -> e -> f e')
         -> (i -> v -> f v')
         -> (Graph i e v -> State (Set i) [Action i e v])
         -> Graph i e v -> f (Graph i e' v')
travActs fe fv trav g = actionsToGraph fe fv $ evalState (trav g) S.empty

-- | Convert a list of actions to a graph using the given applicative functions.
actionsToGraph :: (Ord i, Applicative f)
               => (i -> i -> e -> f e')
               -> (i -> v -> f v')
               -> [Action i e v] -> f (Graph i e' v')
actionsToGraph fe fv acs = construct <$> traverse flat acs
  where
    flat (Vert i v) = Vert i <$> fv i v
    flat (Edge i i' e) = Edge i i' <$> fe i i' e
    act (Vert i v) = addVert i v
    act (Edge i i' e) = addEdge i i' e
    construct acs =
      let (vs, es) = partition (has _Vert) acs
      in foldr act (foldr act empty vs) es

-- | Decompose the graph into the context about the given index/vertex and
-- the remainder of the graph not in the context.
match :: Ord i => i -> v -> Graph i e v -> (Ctxt i e v, Graph i e v)
match i v g = (Ctxt (filter ((/= i) . fst) $ g ^@.. iedgesTo i)
                    v (g ^@.. iedgesFrom i), delIdx i g)

-- | Add the vertex and edges described by the context to the graph. Note that
-- if the context describes edges to/from indices which are not in the graph already
-- then those edges will not be added.
addCtxt :: Ord i => i -> Ctxt i e v -> Graph i e v -> Graph i e v
addCtxt i (Ctxt bef v aft) g =
  foldr (uncurry (i `addEdge`))
    (foldr (uncurry (`addEdge` i)) (addVert i v g) bef)
    aft

-- | A full decomposition of the graph into contexts.
toDecomp :: Ord i => Graph i e v -> Map i (Ctxt i e v)
toDecomp g = fst $ foldr (\(i, v) (cs, g') ->
                                  let (c, g'') = match i v g'
                                  in (M.insert i c cs, g''))
                         (M.empty, g)
                         (g ^@.. iallVerts)

-- | Construct a graph from a decomposition.
fromDecomp :: Ord i => Map i (Ctxt i e v) -> Graph i e v
fromDecomp = foldl (flip (uncurry addCtxt)) empty . M.toList

-- | The isomorphism between graphs and their decompositions.
decomp :: (Ord i, Ord i')
       => Iso (Graph i e v) (Graph i' e' v') (Map i (Ctxt i e v)) (Map i' (Ctxt i' e' v'))
decomp = iso toDecomp fromDecomp

instance (t ~ Graph i' v' e', Ord i) => Rewrapped (Graph i e v) t
instance Ord i => Wrapped (Graph i e v) where
  type Unwrapped (Graph i e v) = Map i (Ctxt i e v)
  _Wrapped' = decomp

instance Functor (Ctxt i e) where
  fmap f = here %~ f

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

scc :: Ord i => Graph i e v -> [[i]]
scc = kosajaru

kosajaru :: Ord i => Graph i e v -> [[i]]
kosajaru g =
  let l = execState (dfsIdx_ (\i -> modify (i:)) g) []
  in filter (not . null) $ fst $ foldr componentFrom ([], reverse g) l
  where
    componentFrom i (comps, g) =
      let comp = execState (dfsFromIdx_ i (\i -> modify (i:)) g) []
      in (comp : comps, filterIdxs (`notElem` comp) g)

t = fromLists [ ('a', 10)
              , ('b', 17)
              , ('c', 8)
              , ('d', 3)
              , ('e', 27)
              , ('f', 4)
              , ('g', 9)
              , ('i', 13)
              ]
              [ ('a', 'b', "this")
              , ('a', 'c', "is")
              , ('b', 'd', "so")
              , ('d', 'f', "neat")
              , ('d', 'g', "cool")
              , ('f', 'g', "swell")
              -- , ('b', 'e', "fun")
              , ('c', 'i', "whoa")
              ]

-- | Traversal variants
-----------------------

idfsVert, ibfsVert :: (Ord i, Applicative f)
                   => (i -> v -> f v') -> Graph i e v -> f (Graph i e v')
idfsVert = idfs (\_ _ -> pure)
ibfsVert = ibfs (\_ _ -> pure)

idfsEdge, ibfsEdge :: (Ord i, Applicative f)
                   => (i -> i -> e -> f e') -> Graph i e v -> f (Graph i e' v)
idfsEdge  fe = idfs fe (const pure)
ibfsEdge  fe = ibfs fe (const pure)

idfs_, ibfs_ :: (Ord i, Applicative f)
             => (i -> i -> e -> f e') -> (i -> v -> f v') -> Graph i e v -> f ()
idfs_ fe fv = void . idfs fe fv
ibfs_ fe fv = void . ibfs fe fv

idfsVert_, ibfsVert_ :: (Applicative f, Ord i)
                     => (i -> v -> f v') -> Graph i e v -> f ()
idfsVert_ fv = void . idfsVert fv
ibfsVert_ fv = void . ibfsVert fv

idfsEdge_, ibfsEdge_ :: (Applicative f, Ord i)
                     => (i -> i -> e -> f e') -> Graph i e v -> f ()
idfsEdge_ fe = void . idfsEdge fe
ibfsEdge_ fe = void . ibfsEdge fe

dfs, bfs :: (Ord i, Applicative f)
         => (e -> f e') -> (v -> f v') -> Graph i e v -> f (Graph i e' v')
dfs fe fv = idfs (\_ _ -> fe) (const fv)
bfs fe fv = ibfs (\_ _ -> fe) (const fv)

dfsVert, bfsVert :: (Applicative f, Ord i)
                 => (v -> f v') -> Graph i e v -> f (Graph i e v')
dfsVert = dfs pure
bfsVert = bfs pure

dfsEdge, bfsEdge :: (Applicative f, Ord i)
                 => (e -> f e') -> Graph i e v -> f (Graph i e' v)
dfsEdge fe = dfs fe pure
bfsEdge fe = bfs fe pure

dfs_, bfs_ :: (Applicative f, Ord i)
           => (e -> f e') -> (v -> f v') -> Graph i e v -> f ()
dfs_ fe fv = void . dfs fe fv
bfs_ fe fv = void . bfs fe fv

dfsVert_, bfsVert_ :: (Ord i, Applicative f)
                   => (v -> f v') -> Graph i e v -> f ()
dfsVert_ fv = void . dfsVert fv
bfsVert_ fv = void . bfsVert fv

dfsEdge_, bfsEdge_ :: (Ord i, Applicative f)
                   => (e -> f e') -> Graph i e v -> f ()
dfsEdge_ fe = void . dfsEdge fe
bfsEdge_ fe = void . bfsEdge fe

dfsIdx_, bfsIdx_ :: (Applicative f, Ord i)
                 => (i -> f i') -> Graph i e v -> f ()
dfsIdx_ fi = void . idfsVert (\i _ -> fi i)
bfsIdx_ fi = void . ibfsVert (\i _ -> fi i)

-- | Maybe traversal variants

itopVert :: (Ord i, Applicative f)
         => (i -> v -> f v') -> Graph i e v -> Maybe (f (Graph i e v'))
itopVert = itop (\_ _ -> pure)

itopEdge :: (Ord i, Applicative f)
         => (i -> i -> e -> f e') -> Graph i e v -> Maybe (f (Graph i e' v))
itopEdge fe = itop fe (const pure)

itop_ :: (Ord i, Applicative f)
      => (i -> i -> e -> f e') -> (i -> v -> f v') -> Graph i e v -> Maybe (f ())
itop_ fe fv g = void <$> itop fe fv g

itopVert_ :: (Applicative f, Ord i)
          => (i -> v -> f v') -> Graph i e v -> Maybe (f ())
itopVert_ fv g = void <$> itopVert fv g

itopEdge_ :: (Applicative f, Ord i)
          => (i -> i -> e -> f e') -> Graph i e v -> Maybe (f ())
itopEdge_ fe g = void <$> itopEdge fe g

top :: (Ord i, Applicative f)
    => (e -> f e') -> (v -> f v') -> Graph i e v -> Maybe (f (Graph i e' v'))
top fe fv = itop (\_ _ -> fe) (const fv)

topVert :: (Applicative f, Ord i)
        => (v -> f v') -> Graph i e v -> Maybe (f (Graph i e v'))
topVert = top pure

topEdge :: (Applicative f, Ord i)
        => (e -> f e') -> Graph i e v -> Maybe (f (Graph i e' v))
topEdge fe = top fe pure

top_ :: (Applicative f, Ord i)
     => (e -> f e') -> (v -> f v') -> Graph i e v -> Maybe (f ())
top_ fe fv g = void <$> top fe fv g

topVert_ :: (Ord i, Applicative f)
         => (v -> f v') -> Graph i e v -> Maybe (f ())
topVert_ fv g = void <$> topVert fv g

topEdge_ :: (Ord i, Applicative f)
         => (e -> f e') -> Graph i e v -> Maybe (f ())
topEdge_ fe g = void <$> topEdge fe g

topIdx_ :: (Applicative f, Ord i)
        => (i -> f i') -> Graph i e v -> Maybe (f ())
topIdx_ fi g = void <$> itopVert (\i _ -> fi i) g

-- | Partial traversals

idfsFromVert, ibfsFromVert :: (Ord i, Applicative f)
                           => i -> (i -> v -> f v) -> Graph i e v -> f (Graph i e v)
idfsFromVert i = idfsFrom i (\_ _ -> pure)
ibfsFromVert i = ibfsFrom i (\_ _ -> pure)

idfsFromEdge, ibfsFromEdge :: (Ord i, Applicative f)
                           => i -> (i -> i -> e -> f e) -> Graph i e v -> f (Graph i e v)
idfsFromEdge i fe = idfsFrom i fe (const pure)
ibfsFromEdge i fe = ibfsFrom i fe (const pure)

idfsFrom_, ibfsFrom_ :: (Ord i, Applicative f)
                     => i -> (i -> i -> e -> f e) -> (i -> v -> f v) -> Graph i e v -> f ()
idfsFrom_ i fe fv = void . idfsFrom i fe fv
ibfsFrom_ i fe fv = void . ibfsFrom i fe fv

idfsFromVert_, ibfsFromVert_ :: (Applicative f, Ord i)
                             => i -> (i -> v -> f v) -> Graph i e v -> f ()
idfsFromVert_ i fv = void . idfsFromVert i fv
ibfsFromVert_ i fv = void . ibfsFromVert i fv

idfsFromEdge_, ibfsFromEdge_ :: (Applicative f, Ord i)
                             => i -> (i -> i -> e -> f e) -> Graph i e v -> f ()
idfsFromEdge_ i fe = void . idfsFromEdge i fe
ibfsFromEdge_ i fe = void . ibfsFromEdge i fe

dfsFrom, bfsFrom :: (Ord i, Applicative f)
                 => i -> (e -> f e) -> (v -> f v) -> Graph i e v -> f (Graph i e v)
dfsFrom i fe fv = idfsFrom i (\_ _ -> fe) (const fv)
bfsFrom i fe fv = ibfsFrom i (\_ _ -> fe) (const fv)

dfsFromVert, bfsFromVert :: (Applicative f, Ord i)
                         => i -> (v -> f v) -> Graph i e v -> f (Graph i e v)
dfsFromVert i = dfsFrom i pure
bfsFromVert i = bfsFrom i pure

dfsFromEdge, bfsFromEdge :: (Applicative f, Ord i)
                         => i -> (e -> f e) -> Graph i e v -> f (Graph i e v)
dfsFromEdge i fe = dfsFrom i fe pure
bfsFromEdge i fe = bfsFrom i fe pure

dfsFrom_, bfsFrom_ :: (Applicative f, Ord i)
                   => i -> (e -> f e) -> (v -> f v) -> Graph i e v -> f ()
dfsFrom_ i fe fv = void . dfsFrom i fe fv
bfsFrom_ i fe fv = void . bfsFrom i fe fv

dfsFromVert_, bfsFromVert_ :: (Ord i, Applicative f)
                   => i -> (v -> f v) -> Graph i e v -> f ()
dfsFromVert_ i fv = void . dfsFromVert i fv
bfsFromVert_ i fv = void . bfsFromVert i fv

dfsFromEdge_, bfsFromEdge_ :: (Ord i, Applicative f)
                           => i -> (e -> f e) -> Graph i e v -> f ()
dfsFromEdge_ i fe = void . dfsFromEdge i fe
bfsFromEdge_ i fe = void . bfsFromEdge i fe

dfsFromIdx_, bfsFromIdx_ :: (Applicative f, Ord i)
                         => i -> (i -> f i') -> Graph i e v -> f ()
dfsFromIdx_ i fi = void . idfsFromVert i (\i v -> fi i *> pure v)
bfsFromIdx_ i fi = void . ibfsFromVert i (\i v -> fi i *> pure v)

-- | Path traversals

ipathVert :: (Ord i, Applicative f)
          => i -> i -> (i -> v -> f v) -> Graph i e v -> Maybe (f (Graph i e v))
ipathVert i1 i2 = ipath i1 i2 (\_ _ -> pure)

ipathEdge :: (Ord i, Applicative f)
          => i -> i -> (i -> i -> e -> f e) -> Graph i e v -> Maybe (f (Graph i e v))
ipathEdge i1 i2 fe = ipath i1 i2 fe (const pure)

ipath_ :: (Ord i, Applicative f)
       => i -> i -> (i -> i -> e -> f e) -> (i -> v -> f v) -> Graph i e v -> Maybe (f ())
ipath_ i1 i2 fe fv g = void <$> ipath i1 i2 fe fv g

ipathVert_ :: (Applicative f, Ord i)
           => i -> i -> (i -> v -> f v) -> Graph i e v -> Maybe (f ())
ipathVert_ i1 i2 fv g = void <$> ipathVert i1 i2 fv g

ipathEdge_ :: (Applicative f, Ord i)
           => i -> i -> (i -> i -> e -> f e) -> Graph i e v -> Maybe (f ())
ipathEdge_ i1 i2 fe g = void <$> ipathEdge i1 i2 fe g

path :: (Ord i, Applicative f)
     => i -> i -> (e -> f e) -> (v -> f v) -> Graph i e v -> Maybe (f (Graph i e v))
path i1 i2 fe fv = ipath i1 i2 (\_ _ -> fe) (const fv)

pathVert :: (Applicative f, Ord i)
         => i -> i -> (v -> f v) -> Graph i e v -> Maybe (f (Graph i e v))
pathVert i1 i2 = path i1 i2 pure

pathEdge :: (Applicative f, Ord i)
         => i -> i -> (e -> f e) -> Graph i e v -> Maybe (f (Graph i e v))
pathEdge i1 i2 fe = path i1 i2 fe pure

path_ :: (Applicative f, Ord i)
      => i -> i -> (e -> f e) -> (v -> f v) -> Graph i e v -> Maybe (f ())
path_ i1 i2 fe fv g = void <$> path i1 i2 fe fv g

pathVert_ :: (Ord i, Applicative f)
          => i -> i -> (v -> f v) -> Graph i e v -> Maybe (f ())
pathVert_ i1 i2 fv g = void <$> pathVert i1 i2 fv g

pathEdge_ :: (Ord i, Applicative f)
         => i -> i -> (e -> f e) -> Graph i e v -> Maybe (f ())
pathEdge_ i1 i2 fe g = void <$> pathEdge i1 i2 fe g

pathIdx_ :: (Applicative f, Ord i)
         => i -> i -> (i -> f i') -> Graph i e v -> Maybe (f ())
pathIdx_ i1 i2 fi g = void <$> ipathVert i1 i2 (\i v -> fi i *> pure v) g