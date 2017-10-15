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
  , vert, allVerts, iallVerts
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
  , idfsFrom, ibfsFrom
  , match, addCtxt
  , toDecomp, fromDecomp, decomp
  ) where

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
import           Data.List (partition)

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

-- | A lens which selects the vertex at the index (if it exists).
vert :: Ord i => i -> Lens' (Graph i e v) (Maybe v)
vert i = vertMap . at i

-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal' (Graph i e v) v
allVerts = vertMap . traverse

-- | Indexed traversal of all vertices.
iallVerts :: IndexedTraversal i (Graph i e v) (Graph i e v') v v'
iallVerts = vertMap . itraverse . indexed

-- | A traversal which selects all edges between two indices.
edges :: Ord i => i -> i -> Traversal' (Graph i e v) e
edges i1 i2 = edgeMap . at i1 . _Just . at i2 . _Just . traverse

-- | A traversal which selects all edges that originate at an index.
edgesFrom :: Ord i => i -> Traversal' (Graph i e v) e
edgesFrom i = edgeMap . at i . _Just . traverse . traverse

-- | A traversal which selects all edges that come from a different index.
edgesTo :: Ord i => i -> Traversal' (Graph i e v) e
edgesTo = iedgesTo

-- | Indexed traversal of the edges from the given index, labelled with the
-- target index.
iedgesFrom :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesFrom i = edgeMap . at i . _Just . mapT . indexed
  where
    mapT f = itraverse (traverse . f)

-- | Indexed traversal of the edges that come from a different index, labelled with
-- the source index.
iedgesTo :: Ord i => i -> IndexedTraversal' i (Graph i e v) e
iedgesTo i = reversed . edgeMap . at i . _Just . mapT i . indexed
  where
    mapT i f = itraverse (traverse . f)

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
idxs = M.keys . view vertMap

-- | The set of all indices in the graph.
idxSet :: Graph i e v -> Set i
idxSet = M.keysSet . view vertMap

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
order g = toEnum $ length (g ^. vertMap)

-- | The number of edges in the graph
size :: Integral n => Graph i e v -> n
size g = toEnum $ length (g ^.. allEdges)

-- | Add a vertex at the index, or replace the vertex at that index.
addVert :: Ord i => i -> v -> Graph i e v -> Graph i e v
addVert i v g = g & vert i .~ Just v

-- | Add an edge between two indices in the graph if both indices have vertices. If
-- they do not, the graph is unchanged.
addEdge :: Ord i => i -> i -> e -> Graph i e v -> Graph i e v
addEdge i1 i2 e g =
  if has _Just (g ^. vert i1) && has _Just (g ^. vert i2)
  then g & edgeMap . at i1 %~ newIfNeeded
         & edgeMap . at i1 . _Just . at i2 %~ newIfNeeded
         & edgeMap . at i1 . _Just . at i2 . _Just %~ (e:)
  else g
    where
      newIfNeeded m = if has _Nothing m then Just mempty else m

-- | Delete all vertices that are equal to the given value.
-- If a vertex is removed, its index and all corresponding edges are also removed.
delVert :: (Eq v, Ord i) => v -> Graph i e v -> Graph i e v
delVert v = filterVerts (not . (==) v)

-- | Remove all edges occurring between two indices.
delEdges :: Ord i => i -> i -> Graph i e v -> Graph i e v
delEdges i1 i2 g = g & edgeMap . at i1 . _Just %~ M.delete i2
                     & edgeMap %~ clearEntry i1

-- | Delete any edges between the two indices which satisfy the predicate.
delEdgeBy :: Ord i => (e -> Bool) -> i -> i -> Graph i e v -> Graph i e v
delEdgeBy p = idelEdgeBy (\i1 i2 -> p)

-- | Delete any edges between the two indices which satisfy the predicate which also
-- takes the edge indices as additional arguments.
idelEdgeBy :: Ord i => (i -> i -> e -> Bool) -> i -> i -> Graph i e v -> Graph i e v
idelEdgeBy p i1 i2 g = g & edgeMap . at i1 . _Just . at i2 . _Just %~ filter (not . p i1 i2)
                        & edgeMap . at i1 . _Just %~ clearEntry i2
                        & edgeMap %~ clearEntry i1

-- | Delete the edge between the two indices with the given value.
delEdge :: (Eq e, Ord i) => i -> i -> e -> Graph i e v -> Graph i e v
delEdge i1 i2 e = delEdgeBy (== e) i1 i2

-- | Remove a index from the graph, deleting the corresponding vertices and
-- edges to and from the index.
delKey :: Ord i => i -> Graph i e v -> Graph i e v
delKey i g = g & vertMap %~ M.delete i
               & edgeMap %~ M.delete i
               & edgeMap . traverse %~ M.delete i
               & edgeMap %~ cleanup

-- | Filter the vertices in the graph by the given predicate.
-- If a vertex is removed, its index and all corresponding edges are also removed.
filterVerts :: Ord i => (v -> Bool) -> Graph i e v -> Graph i e v
filterVerts p g =
  foldr (\(i, v) g' -> if not (p v) then delKey i g' else g') g (g ^@.. iallVerts)

-- | Filter the vertices in the graph by the given predicate which also takes the
-- vertex index as an argument.
-- If a vertex is removed, its index and all corresponding edges are also removed.
ifilterVerts :: Ord i => (i -> v -> Bool) -> Graph i e v -> Graph i e v
ifilterVerts p g =
  foldr (\(i, v) g' -> if not (p i v) then delKey i g' else g') g (g ^@.. iallVerts)

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

-- | Remove all empty entries in a map.
cleanup :: (Ord i, Foldable t) => Map i (t a) -> Map i (t a)
cleanup m = foldr clearEntry m (M.keys m)

-- | If the entry at the index in the map is empty, remove that index from the map.
clearEntry :: (Foldable t, Ord i) => i -> Map i (t a) -> Map i (t a)
clearEntry i m = maybe m (\m' -> if null m' then M.delete i m else m) (M.lookup i m)

-- | Reverse the direction of all edges in the graph.
reverse :: Ord i => Graph i e v -> Graph i e v
reverse g = foldr (\((i1, i2), e) -> addEdge i2 i1 e) init (g ^@.. iallEdges)
  where
    init = Graph (g ^. vertMap) M.empty

instance Ord i => Reversing (Graph i e v) where
  reversing = reverse

instance Functor (Graph i e) where
  fmap f = vertMap %~ fmap f

instance Foldable (Graph i e) where
  foldr f acc g = foldr f acc (g ^. vertMap)

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
  at = vert

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
  fmap f = from edgeFocused . edgeMap %~ fmap (fmap (fmap f))

instance Foldable (EdgeFocused i v) where
  foldr f acc g = foldr f acc (g ^.. from edgeFocused . allEdges)

instance Traversable (EdgeFocused i v) where
  traverse = traverseOf (from edgeFocused . edgeMap . traverse . traverse . traverse)

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

-- | Indexed vertex ttraversal.
itravVerts :: Applicative f => (i -> v -> f v') -> Graph i e v -> f (Graph i e v')
itravVerts = itraverse

-- | Traverse the edges.
travEdges :: Applicative f => (e -> f e') -> Graph i e v -> f (Graph i e' v)
travEdges f g = getEdgeFocused <$> traverse f (EdgeFocused g)

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
reached i = runIdentity . dfsFrom Identity Identity i

-- | The subgraph that reaches the given index.
reaches :: Ord i => i -> Graph i e v -> Graph i e v
reaches i = delEdges i i . reverse . reached i . reverse

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
itop fe fv g =
  let res = execStateT top' ([], S.empty, g)
  in case res of
    Left _ -> Nothing
    Right st -> Just (actionsToGraph fe fv (st ^. _1))

-- | Perform a depth first/breadth first bitraversal of the subgraph reachable
-- from the index. Note that these are not law abiding traversals unless the
-- choice of index has a source vertex.
dfsFrom, bfsFrom :: (Applicative f, Ord i)
                 => (e -> f e')
                 -> (v -> f v')
                 -> i -> Graph i e v -> f (Graph i e' v')
dfsFrom fe fv = idfsFrom (\i1 i2 -> fe) (const fv)
bfsFrom fe fv = ibfsFrom (\i1 i2 -> fe) (const fv)

-- | Perform a depth first/breadth first indexed bitraversal of the subgraph
-- reachable from the index. Note that these are not law abiding traversals unless
-- the choice of index has a source vertex.
idfsFrom, ibfsFrom :: (Applicative f, Ord i)
                   => (i -> i -> e -> f e')
                   -> (i -> v -> f v')
                   -> i -> Graph i e v -> f (Graph i e' v')
idfsFrom fe fv i = travActs fe fv (dfsFrom' i)
ibfsFrom fe fv i = travActs fe fv (bfsFrom' i)

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the graph.
dfs', bfs' :: Ord i => Graph i e v -> State ([Action i e v], Set i) ()
dfs' = promoteFrom dfsFrom'
bfs' = promoteFrom bfsFrom'

-- | Stateful computation which calculates the topological traversal of the graph.
-- This is an implementation of Kahn's algorithm.
top' :: (Eq e, Ord i) => StateT ([Action i e v], Set i, Graph i e v) (Either ()) ()
top' = do
  g <- use _3
  _2 .= noIncoming g
  whileM_ ((not . null) <$> use _2) $ do
    i <- S.findMin <$> use _2
    _2 %= S.delete i
    g <- use _3
    case g ^. at i of
      Nothing -> throwError ()
      Just v -> do
        _1 %= (Vert i v:)
        forM_ (g ^@.. iedgesFrom i) (\(i', e) -> do
          _1 %= (Edge i i' e:)
          g <- _3 <%= delEdge i i' e
          when (null (g ^.. edgesTo i')) (_2 %= S.insert i'))
  g <- use _3
  when (size g > 0) $ throwError ()
  where
    hasIncoming g = S.fromList $ map (snd . fst) $ g ^@.. iallEdges
    noIncoming g = idxSet g `S.difference` hasIncoming g

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the subgraph reached from a
-- particular index.
dfsFrom', bfsFrom' :: Ord i => i -> Graph i e v -> State ([Action i e v], Set i) ()
dfsFrom' i g = do
  s <- use _2
  if i `elem` s then return ()
  else case g ^. at i of
    Nothing -> return ()
    Just v -> do
      _2 %= S.insert i
      _1 %= (Vert i v:)
      mapM_ (\(i', e) -> do
        _1 %= (Edge i i' e:)
        dfsFrom' i' g) (g ^@.. iedgesFrom i)
bfsFrom' start g = knock start >> enter start
  where
    knock i = do
      s <- use _2
      if i `elem` s then return []
      else case g ^. at i of
        Nothing -> return []
        Just v -> do
          _2 %= S.insert i
          _1 %= (Vert i v:)
          return [i]
    enter i = do
      ks <- mapM (\(i', e) -> do
        _1 %= (Edge i i' e:)
        knock i') (g ^@.. iedgesFrom i)
      mapM_ enter (concat ks)

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
  if null s' then return ()
  else do fr (S.findMin s') g
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
match i v g = (Ctxt (g ^@.. iedgesTo i) v (g ^@.. iedgesFrom i), delKey i g)

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
