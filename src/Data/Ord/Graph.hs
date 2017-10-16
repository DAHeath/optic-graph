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

{-|
Module      : Data.Ord.Graph
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
module Data.Ord.Graph
  ( Graph(..), vertMap, edgeMap
  , Ctxt(..), before, here, after
  , allVerts, iallVerts
  , edges, edgesTo, edgesFrom, allEdges
  , iedgesTo, iedgesFrom, iallEdges
  , idxs, idxSet
  , empty, fromLists, union, unionWith
  , order, size
  , addVert, addEdge
  , delVert
  , delEdges, delEdgeBy, delEdge, idelEdgeBy
  , delKey
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
  , Bitraversal, dfs, bfs, top
  , idfs, ibfs, itop, ibitraverse
  , dfsFrom, bfsFrom
  , idfsFrom, ibfsFrom
  , path, ipath
  , match, addCtxt
  , toDecomp, fromDecomp, decomp
  ) where

import           Control.Arrow
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Loops (whileM_)

import           Data.Bifunctor
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition, minimumBy)
import           Data.Maybe (catMaybes)

import           Prelude as P hiding (reverse)

import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as G

data Graph i e v = Graph
  { _vertMap :: Map i v
  , _edgeMap :: Map i (Map i [e])
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
edges :: Ord i => i -> i -> Traversal' (Graph i e v) e
edges i1 i2 = edgeMap . ix i1 . ix i2 . traverse

-- | A traversal which selects all edges that originate at an index.
edgesFrom :: Ord i => i -> Traversal' (Graph i e v) e
edgesFrom i = edgeMap . ix i . traverse . traverse

-- | A traversal which selects all edges that come from a different index.
edgesTo :: Ord i => i -> Traversal' (Graph i e v) e
edgesTo = iedgesTo

-- | Indexed traversal of the edges from the given index, labelled with the
-- target index.
iedgesFrom :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesFrom i = edgeMap . ix i . mapT . indexed
  where
    mapT f = itraverse (traverse . f)

-- | Indexed traversal of the edges that come from a different index, labelled with
-- the source index.
iedgesTo :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesTo i = reversed . edgeMap . ix i . mapT . indexed
  where
    mapT f = itraverse (traverse . f)

-- | A traversal which selects all edges in the graph.
allEdges :: Traversal (Graph i e v) (Graph i e' v) e e'
allEdges = edgeMap . traverse . traverse . traverse

-- | Indexed traversal of all edges in the graph.
iallEdges :: IndexedTraversal (i, i) (Graph i e v) (Graph i e' v) e e'
iallEdges = edgeMap . map1 . indexed
  where
    map1 f = itraverse (map2 f)
    map2 f i = itraverse (\i' -> traverse (f (i, i')))

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

-- | Combine two graphs. If both graph have a vertex at the same index, use the
-- vertex label from the first graph.
union :: Ord i => Graph i e v -> Graph i e v -> Graph i e v
union = unionWith const

-- | Combine two graphs. If both graphs have a vertex at the same index, use the
-- provided function to decide how to generate the new vertex at the index.
unionWith :: Ord i => (v -> v -> v) -> Graph i e v -> Graph i e v -> Graph i e v
unionWith f (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith f v1 v2)
        (M.unionWith (M.unionWith (++)) f1 f2)

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

-- | Add a vertex at the index, or replace the vertex at that index.
addVert :: Ord i => i -> v -> Graph i e v -> Graph i e v
addVert i v = at i ?~ v

-- | Add an edge between two indices in the graph if both indices have vertices. If
-- they do not, the graph is unchanged.
addEdge :: Ord i => i -> i -> e -> Graph i e v -> Graph i e v
addEdge i1 i2 e g = g &
  if has (ix i1) g && has (ix i2) g
  then edgeMap . at i1 . non' _Empty . at i2 . non' _Empty %~ (e:)
  else id

-- | Delete all vertices that are equal to the given value.
-- If a vertex is removed, its index and all corresponding edges are also removed.
delVert :: (Eq v, Ord i) => v -> Graph i e v -> Graph i e v
delVert v = filterVerts (not . (==) v)

-- | Remove all edges occurring between two indices.
delEdges :: Ord i => i -> i -> Graph i e v -> Graph i e v
delEdges i1 i2 = edgeMap . at i1 . non' _Empty . at i2 .~ Nothing

-- | Delete any edges between the two indices which satisfy the predicate.
delEdgeBy :: Ord i => (e -> Bool) -> i -> i -> Graph i e v -> Graph i e v
delEdgeBy p = idelEdgeBy (\i1 i2 -> p)

-- | Delete any edges between the two indices which satisfy the predicate which also
-- takes the edge indices as additional arguments.
idelEdgeBy :: Ord i => (i -> i -> e -> Bool) -> i -> i -> Graph i e v -> Graph i e v
idelEdgeBy p i1 i2 = edgeMap . at i1 . non' _Empty . at i2 . non' _Empty %~ filter (not . p i1 i2)

-- | Delete the edge between the two indices with the given value.
delEdge :: (Eq e, Ord i) => i -> i -> e -> Graph i e v -> Graph i e v
delEdge i1 i2 e = delEdgeBy (== e) i1 i2

-- | Remove a index from the graph, deleting the corresponding vertices and
-- edges to and from the index.
delKey :: Ord i => i -> Graph i e v -> Graph i e v
delKey i g = g & vertMap %~ M.delete i
               & edgeMap %~ M.delete i
               & edgeMap %~ M.mapMaybe ((non' _Empty %~ M.delete i) . Just)

-- | Filter the vertices in the graph by the given predicate.
-- If a vertex is removed, its index and all corresponding edges are also removed.
filterVerts :: Ord i => (v -> Bool) -> Graph i e v -> Graph i e v
filterVerts p = vertMap %~ M.filter p

-- | Filter the vertices in the graph by the given predicate which also takes the
-- vertex index as an argument.
-- If a vertex is removed, its index and all corresponding edges are also removed.
ifilterVerts :: Ord i => (i -> v -> Bool) -> Graph i e v -> Graph i e v
ifilterVerts p = vertMap %~ M.filterWithKey p

-- | Filter the edges in the graph by the given predicate.
filterEdges :: Ord i => (e -> Bool) -> Graph i e v -> Graph i e v
filterEdges p g =
  foldr (\((i1, i2), _) -> delEdgeBy (not . p) i1 i2) g (g ^@.. iallEdges)

-- | Filter the edges in the graph by the given predicate which also takes the
-- edge indices as additional arguments.
ifilterEdges :: Ord i => (i -> i -> e -> Bool) -> Graph i e v -> Graph i e v
ifilterEdges p g =
  foldr (\((i1, i2), _) ->
    idelEdgeBy (\i1 i2 e -> not $ p i1 i2 e) i1 i2) g (g ^@.. iallEdges)

-- | Filter the indices in the graph by the given predicate.
filterIdxs :: Ord i => (i -> Bool) -> Graph i e v -> Graph i e v
filterIdxs p g = foldr delKey g (filter (not . p) (idxs g))

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
  fmap = over (from edgeFocused . edgeMap) . fmap . fmap . fmap

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
      mapT :: Applicative f => Indexed (i, i) e (f e') -> i -> Map i [e] -> f (Map i [e'])
      mapT ix i1 = M.traverseWithKey (\i2 -> traverse (runIndexed ix (i1, i2)))

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
--
-- TODO It seems that the Monad constraint here is necessary due to the nested
-- structure of the edge maps. Is there some way to remove this constraint?
travIdxs :: (Monad f, Ord i, Ord i') => (i -> f i') -> Graph i e v -> f (Graph i' e v)
travIdxs f g =
  let vs' = fIdxs f (g ^. vertMap)
      es' = join $ traverse (fIdxs f) <$> fIdxs f (g ^. edgeMap)
  in Graph <$> vs' <*> es'
  where
    fIdxs :: (Applicative f, Ord i, Ord i') => (i -> f i') -> Map i a -> f (Map i' a)
    fIdxs f m = M.fromList <$> traverse (_1 f) (M.toList m)

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
reached i = runIdentity . dfsFrom i Identity Identity

-- | The subgraph that reaches the given index.
reaches :: Ord i => i -> Graph i e v -> Graph i e v
reaches i = reverse . reached i . reverse

-- | Depth first and breadth first bitraversals of the graph.
dfs, bfs :: Ord i => Bitraversal (Graph i e v) (Graph i e' v') e e' v v'
dfs fe fv = idfs (\_ _ -> fe) (const fv)
bfs fe fv = ibfs (\_ _ -> fe) (const fv)

-- | Topological bitraversal of the graph. If the graph contains cycles,
-- returns Nothing.
top :: (Applicative f, Ord i, Eq e)
     => (e -> f e')
     -> (v -> f v')
     -> Graph i e v -> Maybe (f (Graph i e' v'))
top fe fv = itop (\_ _ -> fe) (const fv)

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
itop :: (Applicative f, Ord i, Eq e)
     => (i -> i -> e -> f e')
     -> (i -> v -> f v')
     -> Graph i e v -> Maybe (f (Graph i e' v'))
itop fe fv g = actionsToGraph fe fv <$> execStateT top' ([], S.empty, g) ^? _Right . _1

-- | Perform a depth first/breadth first bitraversal of the subgraph reachable
-- from the index. Note that these are not law abiding traversals unless the
-- choice of index has a source vertex.
dfsFrom, bfsFrom :: (Applicative f, Ord i)
                 => i
                 -> (e -> f e)
                 -> (v -> f v)
                 -> Graph i e v -> f (Graph i e v)
dfsFrom i fe fv = idfsFrom i (\i1 i2 -> fe) (const fv)
bfsFrom i fe fv = ibfsFrom i (\i1 i2 -> fe) (const fv)

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
  in delEdgesMerge <$> g' <*> pure g
ibfsFrom i fe fv g =
  let g' = travActs fe fv (bfsFrom' i) g
  in delEdgesMerge <$> g' <*> pure g

-- | Delete all edges in the second graph that occur between keys that have
-- edges in the first graph before merging.
delEdgesMerge :: Ord i => Graph i e v -> Graph i e v -> Graph i e v
delEdgesMerge g' g =
  let es = map fst (g' ^@.. iallEdges)
      g'' = foldr (uncurry delEdges) g es
  in g' `union` g''

delEdgeMerge :: (Eq e, Ord i) => Graph i e v -> Graph i e v -> Graph i e v
delEdgeMerge g' g =
  let es = g' ^@.. iallEdges
      g'' = foldr (\((i1, i2), e) -> delEdge i1 i2 e) g es
  in g' `union` g''

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the graph.
dfs', bfs' :: Ord i => Graph i e v -> State ([Action i e v], Set i) ()
dfs' = promoteFrom dfsFrom'
bfs' = promoteFrom bfsFrom'

-- | Stateful computation which calculates the topological traversal of the graph.
-- This is an implementation of Kahn's algorithm.
top' :: (Eq e, Ord i) => StateT ([Action i e v], Set i, Graph i e v) (Either ()) ()
top' = do
  set <~ uses graph noIncoming
  whileM_ (uses set $ not . null) $ do
    i <- zoom set $ state S.deleteFindMin
    g <- use graph
    case g ^. at i of
      Nothing -> throwError ()
      Just v -> do
        acs %= (Vert i v:)
        forM_ (g ^@.. iedgesFrom i) $ \(i', e) -> do
          acs %= (Edge i i' e:)
          g <- graph <%= delEdge i i' e
          when (hasn't (edgesTo i') g) (set %= S.insert i')
  g <- use graph
  when (size g > 0) $ throwError ()
  where
    hasIncoming g = S.fromList $ map (snd . fst) $ g ^@.. iallEdges
    noIncoming g = idxSet g `S.difference` hasIncoming g
    acs = _1
    set = _2
    graph = _3

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the subgraph reached from a
-- particular index.
dfsFrom', bfsFrom' :: Ord i => i -> Graph i e v -> State ([Action i e v], Set i) ()
dfsFrom' i g = do
  b <- set . contains i <<.= True
  unless b $
    forOf_ (ix i) g $ \v -> do
      acs %= (Vert i v:)
      forM_ (g ^@.. iedgesFrom i) $ \(i', e) -> do
        acs %= (Edge i i' e:)
        dfsFrom' i' g
  where
    acs = _1
    set = _2
bfsFrom' start g = evalStateT (visit start >> loop) []
  where
    loop =
      whileM_ (gets $ not . null) $ do
        i <- state (head &&& tail)
        forM_ (g ^@.. iedgesFrom i) $ \(i', e) -> do
          lift (acs %= (Edge i i' e:))
          visit i'
    visit i = do
      b <- lift (use $ set . contains i)
      unless b $ case g ^. at i of
        Nothing -> return ()
        Just v -> do
          lift (set %= S.insert i)
          lift (acs %= (Vert i v:))
          modify (++ [i])
    acs = _1
    set = _2

-- | Bitraversal of a path between the two given indices (if one exists).
--
-- Note that as a side-effect, this will delete any edges that appear along the
-- path if they are an exact duplicate of an edge in the traversal (the same indices
-- and equal under (==)).
path :: (Applicative f, Ord i, Eq e) => i -> i
     -> (e -> f e)
     -> (v -> f v)
     -> Graph i e v -> Maybe (f (Graph i e v))
path i1 i2 fe fv = ipath i1 i2 (\_ _ -> fe) (const fv)

-- | Indexed bitraversal of a path between the two given indices (if one exists).
--
-- Note that as a side-effect, this will delete any edges that appear along the
-- path if they are an exact duplicate of an edge in the traversal (the same indices
-- and equal under (==)).
ipath :: (Applicative f, Ord i, Eq e) => i -> i
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
      else
        case M.lookup i m of
          Nothing -> Nothing
          Just (i', e, v) -> do
            acs <- recAcs m i'
            return (Vert i v : Edge i' i e : acs)

-- | Bellman Ford shortest path from the given index. The result is a map of
-- the index to the information required to reconstruct the path the index's
-- predecessor to the index (specifically the incoming edge and the index's
-- vertex).
dijkstra', bellmanFord' :: (Ord i, Ord n, Num n) => (e -> n) -> i -> Graph i e v
                         -> Maybe (Map i (i, e, v))
dijkstra' weight i g = either (const Nothing) (Just . view _1) $ execStateT (do
  dists . at i ?= 0
  whileM_ (uses iSet $ not . null) $ do
    ds <- use dists
    near <- minimumBy (\i1 i2 -> cmp (M.lookup i1 ds) (M.lookup i2 ds)) . S.toList <$> use iSet
    iSet %= S.delete near
    forM_ (g ^@.. iedgesFrom near) $ \(i', e) -> do
      ds <- use dists
      let alt = (+ weight e) <$> M.lookup near ds
      when (cmp alt (M.lookup i' ds) ==  LT) $
        case g ^. at i' of
          Nothing -> throwError ()
          Just v -> do
            dists . at i' .= alt
            actsTo . at i' ?= (near, e, v)
  ) (M.empty, M.empty, idxSet g)
  where
    actsTo = _1
    dists = _2
    iSet = _3
    cmp md1 md2 = maybe GT (\d1 -> maybe LT (compare d1) md2) md1

bellmanFord' weight i g = either (const Nothing) (Just . fst) $ execStateT (do
  dists . at i .= Just 0
  forM_ (g ^.. allVerts) $ \_ ->
    iterEdgeWeights $ \i1 i2 e d ->
      case g ^. at i2 of
        Nothing -> throwError ()
        Just v -> do
          dists . at i2 ?= d
          actsTo . at i2 ?= (i1, e, v)
  iterEdgeWeights (\_ _ _ _ -> throwError ())) (M.empty, M.empty)
  where
    -- call the action when a lower weight path is found
    iterEdgeWeights ac =
      forM_ (g ^@.. iallEdges) $ \((i1, i2), e) -> do
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
            => (i -> Graph i e v -> State ([Action i e v], Set i) ())
            -> Graph i e v -> State ([Action i e v], Set i) ()
promoteFrom fr g = do
  let ks = idxSet g
  s <- use _2
  let s' = S.difference ks s
  unless (null s') $ do
    fr (S.findMin s') g
    promoteFrom fr g

-- | Promote a stateful generator of graph actions to a indexed bitraversal.
travActs :: (Ord i, Applicative f)
         => (i -> i -> e -> f e')
         -> (i -> v -> f v')
         -> (Graph i e v -> State ([Action i e v], Set i) ())
         -> Graph i e v -> f (Graph i e' v')
travActs fe fv trav g =
  let acs = fst (execState (trav g) ([], S.empty))
  in actionsToGraph fe fv acs

-- | Convert a list of actions to a graph using the given applicative functions.
actionsToGraph :: (Ord i, Applicative f)
               => (i -> i -> e -> f e')
               -> (i -> v -> f v')
               -> [Action i e v] -> f (Graph i e' v')
actionsToGraph fe fv acs = construct <$> traverse flat (acs ^. reversed)
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
                    v (g ^@.. iedgesFrom i), delKey i g)

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

