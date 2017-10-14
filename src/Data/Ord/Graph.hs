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
module Data.Ord.Graph
  ( Graph(..), vertMap, edgeMap
  , Ctxt(..), before, here, after
  , vert, allVerts, allLabVerts
  , edges, edgesFrom, allEdges, labEdgesTo, labEdgesFrom, allLabEdges
  , keys, keysSet
  , empty, union, unionWith
  , order, size
  , addVert, addEdge
  , delVert
  , delEdges, delEdgeBy, delEdge, idelEdgeBy
  , delKey
  , filterVerts, ifilterVerts
  , filterEdges, ifilterEdges
  , filterKeys
  , reverse
  , EdgeFocused(..), edgeFocused
  , mapVerts, imapVerts
  , mapEdges, imapEdges
  , mapKeys
  , foldVerts, ifoldVerts
  , foldEdges, ifoldEdges
  , foldKeys
  , travVerts, itravVerts
  , travEdges, itravEdges
  , travKeys
  , reaches, reached
  , Bitraversal, dfs, bfs
  , idfs, ibfs, ibitraverse
  , idfsFrom, ibfsFrom
  , match, addCtxt
  , toDecomp, fromDecomp, decomp
  ) where

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
import           Data.List (partition)

import           Prelude as P hiding (reverse)

import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as G

data Graph k e v = Graph
  { _vertMap :: Map k v
  , _edgeMap :: Map k (Map k [e])
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

data Ctxt k e v = Ctxt
  { _before :: [(k, e)]
  , _here :: v
  , _after :: [(k, e)]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Ctxt

-- | To simplify the implementation of traversals, we record the order in which
-- the graph short be modified.
data Action k e v
  = Vert k v
  | Edge k k e
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Action

-- | A lens which selects the vertex at the key (if it exists).
vert :: Ord k => k -> Lens' (Graph k e v) (Maybe v)
vert k = vertMap . at k

-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal' (Graph k e v) v
allVerts = vertMap . traverse

-- | Indexed traversal of all vertices with their keys.
allLabVerts :: IndexedTraversal k (Graph k e v) (Graph k e v') v v'
allLabVerts = vertMap . itraverse . indexed

-- | A traversal which selects all edges between two keys.
edges :: Ord k => k -> k -> Traversal' (Graph k e v) e
edges k1 k2 = edgeMap . at k1 . _Just . at k2 . _Just . traverse

-- | A traversal which selects all edges that originate at a key.
edgesFrom :: Ord k => k -> Traversal' (Graph k e v) e
edgesFrom k = edgeMap . at k . _Just . traverse . traverse

-- | Indexed traversal of the edges from the given key, labelled with their target
-- key.
labEdgesFrom :: Ord k => k -> IndexedTraversal' k (Graph k e v) e
labEdgesFrom k = edgeMap . at k . _Just . mapT . indexed
  where
    mapT f = itraverse (traverse . f)

-- | The edges to the given key, labelled with their source key.
labEdgesTo :: Ord k => Graph k e v -> k -> [(k, e)]
labEdgesTo g k = filter (\(k', _) -> k' /= k) $ reverse g ^@.. labEdgesFrom k

-- | A traversal which selects all edges in the graph.
allEdges :: Traversal (Graph k e v) (Graph k e' v) e e'
allEdges = edgeMap . traverse . traverse . traverse

-- | Indexed traversal of all edges in the graph, labelled with their keys.
allLabEdges :: IndexedTraversal (k, k) (Graph k e v) (Graph k e' v) e e'
allLabEdges = edgeMap . map1 . indexed
  where
    map1 f = itraverse (map2 f)
    map2 f k = itraverse (\k' -> traverse (f (k, k')))

-- | Keys of the graph in ascending order.
keys :: Graph k e v -> [k]
keys = M.keys . view vertMap

-- | The set of all keys in the graph.
keysSet :: Graph k e v -> Set k
keysSet = M.keysSet . view vertMap

-- | A graph with no vertices and no edges.
empty :: Graph k e v
empty = Graph M.empty M.empty

-- | Combine two graphs. If both graph have a vertex at the same key, use the
-- vertex label from the first graph.
union :: Ord k => Graph k e v -> Graph k e v -> Graph k e v
union = unionWith const

-- | Combine two graphs. If both graphs have a vertex at the same key, use the
-- provided function to decide how to generate the new vertex at the key.
unionWith :: Ord k => (v -> v -> v) -> Graph k e v -> Graph k e v -> Graph k e v
unionWith f (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith f v1 v2)
        (M.unionWith (M.unionWith (++)) f1 f2)

instance Ord k => Monoid (Graph k e v) where
  mempty = empty
  mappend = union

instance Ord k => Semigroup (Graph k e v)
instance AsEmpty (Graph k e v) where
  _Empty = nearly empty (\g -> null (g ^. vertMap) && null (g ^. edgeMap))

-- | The number of vertices in the graph.
order :: Integral i => Graph k e v -> i
order g = toEnum $ length (g ^. vertMap)

-- | The number of edges in the graph
size :: Integral i => Graph k e v -> i
size g = toEnum $ length (g ^.. allEdges)

-- | Add a vertex at the key, or replace the vertex at that key.
addVert :: Ord k => k -> v -> Graph k e v -> Graph k e v
addVert k v g = g & vert k .~ Just v

-- | Add an edge between two keys in the graph if both keys have vertices. If
-- they do not, the graph is unchanged.
addEdge :: Ord k => k -> k -> e -> Graph k e v -> Graph k e v
addEdge k1 k2 e g =
  if has _Just (g ^. vert k1) && has _Just (g ^. vert k2)
  then g & edgeMap . at k1 %~ newIfNeeded
         & edgeMap . at k1 . _Just . at k2 %~ newIfNeeded
         & edgeMap . at k1 . _Just . at k2 . _Just %~ (e:)
  else g
    where
      newIfNeeded m = if has _Nothing m then Just mempty else m

-- | Delete all vertices that are equal to the given value.
-- If a vertex is removed, its key and all corresponding edges are also removed.
delVert :: (Eq v, Ord k) => v -> Graph k e v -> Graph k e v
delVert v = filterVerts (not . (==) v)

-- | Remove all edges occurring between two keys.
delEdges :: Ord k => k -> k -> Graph k e v -> Graph k e v
delEdges k1 k2 g = g & edgeMap . at k1 . _Just %~ M.delete k2
                     & edgeMap %~ clearEntry k1

-- | Delete any edges between the two keys which satisfy the predicate.
delEdgeBy :: Ord k => (e -> Bool) -> k -> k -> Graph k e v -> Graph k e v
delEdgeBy p = idelEdgeBy (\k1 k2 -> p)

-- | Delete any edges between the two keys which satisfy the predicate which also
-- takes the edge keys as additional arguments.
idelEdgeBy :: Ord k => (k -> k -> e -> Bool) -> k -> k -> Graph k e v -> Graph k e v
idelEdgeBy p k1 k2 g = g & edgeMap . at k1 . _Just . at k2 . _Just %~ filter (not . p k1 k2)
                        & edgeMap . at k1 . _Just %~ clearEntry k2
                        & edgeMap %~ clearEntry k1

-- | Delete the edge between the two keys with the given value.
delEdge :: (Eq e, Ord k) => k -> k -> e -> Graph k e v -> Graph k e v
delEdge k1 k2 e = delEdgeBy (== e) k1 k2

-- | Remove a key from the graph, deleting the corresponding vertices and
-- edges to and from the key.
delKey :: Ord k => k -> Graph k e v -> Graph k e v
delKey k g = g & vertMap %~ M.delete k
               & edgeMap %~ M.delete k
               & edgeMap . traverse %~ M.delete k
               & edgeMap %~ cleanup

-- | Filter the vertices in the graph by the given predicate.
-- If a vertex is removed, its key and all corresponding edges are also removed.
filterVerts :: Ord k => (v -> Bool) -> Graph k e v -> Graph k e v
filterVerts p g =
  foldr (\(k, v) g' -> if not (p v) then delKey k g' else g') g (g ^@.. allLabVerts)

-- | Filter the vertices in the graph by the given predicate which also takes the
-- vertex key as an argument.
-- If a vertex is removed, its key and all corresponding edges are also removed.
ifilterVerts :: Ord k => (k -> v -> Bool) -> Graph k e v -> Graph k e v
ifilterVerts p g =
  foldr (\(k, v) g' -> if not (p k v) then delKey k g' else g') g (g ^@.. allLabVerts)

-- | Filter the edges in the graph by the given predicate.
filterEdges :: Ord k => (e -> Bool) -> Graph k e v -> Graph k e v
filterEdges p g =
  foldr (\((k1, k2), _) -> delEdgeBy (not . p) k1 k2) g (g ^@.. allLabEdges)

-- | Filter the edges in the graph by the given predicate which also takes the
-- edge keys as additional arguments.
ifilterEdges :: Ord k => (k -> k -> e -> Bool) -> Graph k e v -> Graph k e v
ifilterEdges p g =
  foldr (\((k1, k2), _) ->
    idelEdgeBy (\k1 k2 e -> not $ p k1 k2 e) k1 k2) g (g ^@.. allLabEdges)

-- | Filter the keys in the graph by the given predicate.
filterKeys :: Ord k => (k -> Bool) -> Graph k e v -> Graph k e v
filterKeys p g = foldr delKey g (filter (not . p) (keys g))

-- | Remove all empty entries in a map.
cleanup :: (Ord k, Foldable t) => Map k (t a) -> Map k (t a)
cleanup m = foldr clearEntry m (M.keys m)

-- | If the entry at the key in the map is empty, remove that key from the map.
clearEntry :: (Foldable t, Ord k) => k -> Map k (t a) -> Map k (t a)
clearEntry k m = maybe m (\m' -> if null m' then M.delete k m else m) (M.lookup k m)

-- | Reverse the direction of all edges in the graph.
reverse :: Ord k => Graph k e v -> Graph k e v
reverse g = foldr (\((k1, k2), e) -> addEdge k2 k1 e) init (g ^@.. allLabEdges)
  where
    init = Graph (g ^. vertMap) M.empty

instance Ord k => Reversing (Graph k e v) where
  reversing = reverse

instance Functor (Graph k e) where
  fmap f = vertMap %~ fmap f

instance Foldable (Graph k e) where
  foldr f acc g = foldr f acc (g ^. vertMap)

instance Traversable (Graph k e) where
  traverse = traverseOf (vertMap . traverse)

instance (k ~ k', e ~ e') => Each (Graph k e v) (Graph k' e' v') v v' where
  each = traversed

instance FunctorWithIndex k (Graph k e)
instance FoldableWithIndex k (Graph k e)
instance TraversableWithIndex k (Graph k e) where
  itraverse = itraverseOf (vertMap . itraverse . runIndexed)

type instance Index (Graph k e v) = k
type instance IxValue (Graph k e v) = v
instance Ord k => Ixed (Graph k e v)
instance Ord k => At (Graph k e v) where
  at = vert

-- | By default, graphs are "focused" on the vertices, meaning that common
-- typeclass instances act on the vertices. EdgeFocused provides an alternative
-- representation where the edges are the focus of the typeclasses.
newtype EdgeFocused k v e = EdgeFocused { getEdgeFocused :: Graph k e v }
  deriving (Show, Read, Eq, Ord, Data)

-- | Isomorphism between the graph and its edge focused equivalent.
edgeFocused :: Iso (Graph k e v) (Graph k' e' v')
                   (EdgeFocused k v e) (EdgeFocused k' v' e')
edgeFocused = iso EdgeFocused getEdgeFocused

instance Functor (EdgeFocused k v) where
  fmap f = from edgeFocused . edgeMap %~ fmap (fmap (fmap f))

instance Foldable (EdgeFocused k v) where
  foldr f acc g = foldr f acc (g ^.. from edgeFocused . allEdges)

instance Traversable (EdgeFocused k v) where
  traverse = traverseOf (from edgeFocused . edgeMap . traverse . traverse . traverse)

instance (k ~ k', v ~ v') => Each (EdgeFocused k v e) (EdgeFocused k' v' e') e e' where
  each = traversed

instance FunctorWithIndex (k, k) (EdgeFocused k v)
instance FoldableWithIndex (k, k) (EdgeFocused k v)
instance TraversableWithIndex (k, k) (EdgeFocused k v) where
  itraverse = itraverseOf (from edgeFocused . edgeMap . itraverse . mapT)
    where
      mapT :: Applicative f => Indexed (k, k) e (f e') -> k -> Map k [e] -> f (Map k [e'])
      mapT ix k1 = M.traverseWithKey (\k2 -> traverse (runIndexed ix (k1, k2)))

-- | Apply the given function to all vertices.
mapVerts :: (v -> v') -> Graph k e v -> Graph k e v'
mapVerts = fmap

-- | Apply the given function to all vertices, taking each vertex's key as an
-- additional argument.
imapVerts :: (k -> v -> v') -> Graph k e v -> Graph k e v'
imapVerts = imap

-- | Apply the given function to all edges.
mapEdges :: (e -> e') -> Graph k e v -> Graph k e' v
mapEdges = under (from edgeFocused) . fmap

-- | Apply the given function to all edges, taking each edge's keys as
-- additional arguments.
imapEdges :: (k -> k -> e -> e') -> Graph k e v -> Graph k e' v
imapEdges = under (from edgeFocused) . imap . uncurry

-- | The map obtained by applying f to each key of s.
-- The size of the result may be smaller if f maps two or more distinct keys to
-- the same new key. In this case the value at the greatest of the original keys
-- is retained.
mapKeys :: Ord k' => (k -> k') -> Graph k e v -> Graph k' e v
mapKeys f (Graph vs es) =
  Graph (M.mapKeys f vs)
        (M.mapKeys f $ fmap (M.mapKeys f) es)

-- | Aggregate the vertices.
foldVerts :: (v -> b -> b) -> b -> Graph k e v -> b
foldVerts = foldr

-- | Aggregate the vertices with vertex keys as an additional argument.
ifoldVerts :: (k -> v -> b -> b) -> b -> Graph k e v -> b
ifoldVerts = ifoldr

-- | Aggregate the edges.
foldEdges :: (e -> b -> b) -> b -> Graph k e v -> b
foldEdges f acc g = foldr f acc (EdgeFocused g)

-- | Aggregate the edges with edge keys as an additional arguments.
ifoldEdges :: (k -> k -> e -> b -> b) -> b -> Graph k e v -> b
ifoldEdges f acc g = ifoldr (uncurry f) acc (EdgeFocused g)

-- | Aggregate the keys.
foldKeys :: (k -> b -> b) -> b -> Graph k e v -> b
foldKeys f acc g = foldr f acc (keys g)

-- | Traverse the vertices.
travVerts :: Applicative f => (v -> f v') -> Graph k e v -> f (Graph k e v')
travVerts = traverse

-- | Indexed vertex ttraversal.
itravVerts :: Applicative f => (k -> v -> f v') -> Graph k e v -> f (Graph k e v')
itravVerts = itraverse

-- | Traverse the edges.
travEdges :: Applicative f => (e -> f e') -> Graph k e v -> f (Graph k e' v)
travEdges f g = getEdgeFocused <$> traverse f (EdgeFocused g)

-- | Indexed edge traversal.
itravEdges :: Applicative f => (k -> k -> e -> f e') -> Graph k e v -> f (Graph k e' v)
itravEdges f g = getEdgeFocused <$> itraverse (uncurry f) (EdgeFocused g)

-- | Traverse the keys.
-- The size of the result may be smaller if f maps two or more distinct keys to
-- the same new key. In this case the value at the greatest of the original keys
-- is retained.
--
-- TODO It seems that the Monad constraint here is necessary due to the nested
-- structure of the edge maps. Is there some way to remove this constraint?
travKeys :: (Monad f, Ord k, Ord k') => (k -> f k') -> Graph k e v -> f (Graph k' e v)
travKeys f g =
  let vs' = fKeys f (g ^. vertMap)
      es' = join $ traverse (fKeys f) <$> fKeys f (g ^. edgeMap)
  in Graph <$> vs' <*> es'
  where
    fKeys :: (Applicative f, Ord k, Ord k') => (k -> f k') -> Map k a -> f (Map k' a)
    fKeys f m = M.fromList <$> traverse (_1 f) (M.toList m)

instance Bifunctor (Graph k) where
  bimap fe fv = mapVerts fv . mapEdges fe

instance Bifoldable (Graph k) where
  bifoldr fe fv acc g = execState (bitraverse_ (modify . fe) (modify . fv) g) acc

instance Ord k => Bitraversable (Graph k) where
  bitraverse = dfs

type Bitraversal s t a b c d =
  forall f. Applicative f => (a -> f b) -> (c -> f d) -> s -> f t

-- | The subgraph reached from the given key.
reached :: Ord k => k -> Graph k e v -> Graph k e v
reached k = runIdentity . dfsFrom Identity Identity k

-- | The subgraph that reaches the given key.
reaches :: Ord k => k -> Graph k e v -> Graph k e v
reaches k = delEdges k k . reverse . reached k . reverse

-- | Depth first and breadth first bitraversals of the graph.
dfs, bfs :: Ord k => Bitraversal (Graph k e v) (Graph k e' v') e e' v v'
dfs fe fv = idfs (\k1 k2 -> fe) (const fv)
bfs fe fv = ibfs (\k1 k2 -> fe) (const fv)

-- | Depth first and breadth first indexed bitraversals of the graph.
idfs, ibfs, ibitraverse :: (Applicative f, Ord k)
                        => (k -> k -> e -> f e')
                        -> (k -> v -> f v')
                        -> Graph k e v -> f (Graph k e' v')
idfs fe fv = travActs fe fv dfs'
ibfs fe fv = travActs fe fv bfs'
ibitraverse = idfs

-- | Perform a depth first/breadth first bitraversal of the subgraph reachable
-- from the key. Note that these are not law abiding traversals unless the
-- choice of key has a source vertex.
dfsFrom, bfsFrom :: (Applicative f, Ord k)
                 => (e -> f e')
                 -> (v -> f v')
                 -> k -> Graph k e v -> f (Graph k e' v')
dfsFrom fe fv = idfsFrom (\k1 k2 -> fe) (const fv)
bfsFrom fe fv = ibfsFrom (\k1 k2 -> fe) (const fv)

-- | Perform a depth first/breadth first indexed bitraversal of the subgraph
-- reachable from the key. Note that these are not law abiding traversals unless
-- the choice of key has a source vertex.
idfsFrom, ibfsFrom :: (Applicative f, Ord k)
                   => (k -> k -> e -> f e')
                   -> (k -> v -> f v')
                   -> k -> Graph k e v -> f (Graph k e' v')
idfsFrom fe fv k = travActs fe fv (dfsFrom' k)
ibfsFrom fe fv k = travActs fe fv (bfsFrom' k)

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the graph.
dfs', bfs' :: Ord k => Graph k e v -> State ([Action k e v], Set k) ()
dfs' = promoteFrom dfsFrom'
bfs' = promoteFrom bfsFrom'

-- | Stateful computations which calculate the actions needed to perform a
-- depth first/breadth first traversal of the subgraph reached from a
-- particular key.
dfsFrom', bfsFrom' :: Ord k => k -> Graph k e v -> State ([Action k e v], Set k) ()
dfsFrom' k g = do
  s <- use _2
  if k `elem` s then return ()
  else case g ^. at k of
    Nothing -> return ()
    Just v -> do
      _2 %= S.insert k
      _1 %= (Vert k v:)
      mapM_ (\(k', e) -> do
        _1 %= (Edge k k' e:)
        dfsFrom' k' g) (g ^@.. labEdgesFrom k)
bfsFrom' start g = knock start >> enter start
  where
    knock k = do
      s <- use _2
      if k `elem` s then return []
      else case g ^. at k of
        Nothing -> return []
        Just v -> do
          _2 %= S.insert k
          _1 %= (Vert k v:)
          return [k]
    enter k = do
      ks <- mapM (\(k', e) -> do
        _1 %= (Edge k k' e:)
        knock k') (g ^@.. labEdgesFrom k)
      mapM_ enter (concat ks)

-- | Promote a partial traversal (which only reaches a portion of the graph) to
-- a full traversal by repeatedly invoking the partial traversal on non-visited
-- keys.
promoteFrom :: Ord k
            => (k -> Graph k e v -> State ([Action k e v], Set k) ())
            -> Graph k e v -> State ([Action k e v], Set k) ()
promoteFrom fr g = do
  let ks = keysSet g
  s <- use _2
  let s' = S.difference ks s
  if null s' then return ()
  else do fr (S.findMin s') g
          promoteFrom fr g

-- | Promote a stateful generator of graph actions to a indexed bitraversal.
travActs :: (Ord k, Applicative f)
         => (k -> k -> e -> f e')
         -> (k -> v -> f v')
         -> (Graph k e v -> State ([Action k e v], Set k) ())
         -> Graph k e v -> f (Graph k e' v')
travActs fe fv trav g =
  let acs = fst (execState (trav g) ([], S.empty)) ^. reversed
  in construct <$> traverse flat acs
  where
    flat (Vert k v) = Vert k <$> fv k v
    flat (Edge k k' e) = Edge k k' <$> fe k k' e
    act (Vert k v) = addVert k v
    act (Edge k k' e) = addEdge k k' e
    construct acs =
      let (vs, es) = partition (has _Vert) acs
      in foldr act (foldr act empty vs) es

-- | Decompose the graph into the context about the given key/vertex and
-- the remainder of the graph not in the context.
match :: Ord k => k -> v -> Graph k e v -> (Ctxt k e v, Graph k e v)
match k v g = (Ctxt (labEdgesTo g k) v (g ^@.. labEdgesFrom k), delKey k g)

-- | Add the vertex and edges described by the context to the graph. Note that
-- if the context describes edges to/from keys which are not in the graph already
-- then those edges will not be added.
addCtxt :: Ord k => k -> Ctxt k e v -> Graph k e v -> Graph k e v
addCtxt k (Ctxt bef v aft) g =
  foldr (uncurry (k `addEdge`))
    (foldr (uncurry (`addEdge` k)) (addVert k v g) bef)
    aft

-- | A full decomposition of the graph into contexts.
toDecomp :: Ord k => Graph k e v -> Map k (Ctxt k e v)
toDecomp g = fst $ foldr (\(k, v) (cs, g') ->
                                  let (c, g'') = match k v g'
                                  in (M.insert k c cs, g''))
                         (M.empty, g)
                         (g ^@.. allLabVerts)

-- | Construct a graph from a decomposition.
fromDecomp :: Ord k => Map k (Ctxt k e v) -> Graph k e v
fromDecomp = foldl (flip (uncurry addCtxt)) empty . M.toList

-- | The isomorphism between graphs and their decompositions.
decomp :: (Ord k, Ord k')
       => Iso (Graph k e v) (Graph k' e' v') (Map k (Ctxt k e v)) (Map k' (Ctxt k' e' v'))
decomp = iso toDecomp fromDecomp

instance (t ~ Graph k' v' e', Ord k) => Rewrapped (Graph k e v) t
instance Ord k => Wrapped (Graph k e v) where
  type Unwrapped (Graph k e v) = Map k (Ctxt k e v)
  _Wrapped' = decomp

instance Functor (Ctxt k e) where
  fmap f = here %~ f

instance (Ord k, Arbitrary k, Arbitrary e, Arbitrary v) => Arbitrary (Graph k e v) where
  arbitrary = do
    ks <- arbitrary
    vs <- arbVerts ks
    es <- if null ks then return [] else G.listOf (arbEdge ks)
    return (foldr (\(k1, k2, e) -> addEdge k1 k2 e) (foldr (uncurry addVert) empty vs) es)
    where
      arbVerts = traverse (\k -> (\v -> (k, v)) <$> arbitrary)
      arbEdge ks = do
        k1 <- G.elements ks
        k2 <- G.elements ks
        e <- arbitrary
        return (k1, k2, e)
  shrink = const []

test =
  let g1 = addVert 0 "hello" empty
      g2 = addVert 1 "world" g1
      g3 = addVert 2 "sup" g2
      g4 = addEdge 0 1 4.3 g3
      g5 = addEdge 0 1 7.7 g4
      g6 = addEdge 1 0 5.1 g5
      g7 = addEdge 1 2 1.2 g6
  in g7

emit = bitraverse (\e -> print e >> return e)
                  (\v -> print v >> return v)

emit' = ibfsFrom (\k1 k2 e -> print k1 >> print k2 >> print e)
                 (\k e -> print k >> print e)
