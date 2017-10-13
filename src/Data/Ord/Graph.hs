{-# LANGUAGE ApplicativeDo
           , TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , MultiParamTypeClasses
           , RankNTypes
           , LambdaCase
           , TupleSections
           , NoMonomorphismRestriction
           #-}
module Data.Ord.Graph where

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

import           Prelude hiding (reverse)

data Graph k e v = Graph
  { _vertMap :: Map k v
  , _edgeMap :: Map k (Map k [e])
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

data Ctxt k e v = Ctxt
  { _before :: [(k, e)]
  , _here :: (k, v)
  , _after :: [(k, e)]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Ctxt

-- | A lens which selects the vertex at the key (if it exists).
vert :: Ord k => k -> Lens' (Graph k e v) (Maybe v)
vert k = vertMap . at k

-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal' (Graph k e v) v
allVerts = vertMap . traverse

-- | The vertices of the graph, labelled with their keys.
allLabVerts :: Graph k e v -> [(k, v)]
allLabVerts g = M.toList $ g ^. vertMap

-- | A traversal which selects all edges between two keys.
edges :: Ord k => k -> k -> Traversal' (Graph k e v) e
edges k1 k2 = edgeMap . at k1 . _Just . at k2 . _Just . traverse

-- | A traversal which selects all edges that originate at a key.
edgesFrom :: Ord k => k -> Traversal' (Graph k e v) e
edgesFrom k = edgeMap . at k . _Just . traverse . traverse

-- | A traversal which selects all edges in the graph.
allEdges :: Traversal' (Graph k e v) e
allEdges = edgeMap . traverse . traverse . traverse

-- | The edges from the given key, labelled with their target key.
labEdgesFrom :: Ord k => Graph k e v -> k -> [(k, e)]
labEdgesFrom g k = case M.lookup k (g ^. edgeMap) of
  Nothing -> []
  Just m -> concatMap (\(v, es) -> map (v,) es) (M.toList m)

-- | The edges to the given key, labelled with their source key.
labEdgesTo :: Ord k => Graph k e v -> k -> [(k, e)]
labEdgesTo = labEdgesFrom . reverse

-- | All edges in the graph, labelled with their source and target keys.
allLabEdges :: Ord k => Graph k e v -> [(k, k, e)]
allLabEdges g = concatMap (\k1 -> do
    (k2, e) <- labEdgesFrom g k1
    return (k1, k2, e)) (keys g)

-- | Keys of the graph in ascending order.
keys :: Graph k e v -> [k]
keys = M.keys . view vertMap

-- | The set of all keys in the graph.
keysSet :: Graph k e v -> Set k
keysSet = M.keysSet . view vertMap

-- | A graph with no vertices and no edges.
empty :: Graph k e v
empty = Graph M.empty M.empty

-- | Combine two graphs. If both graphs have a vertex at the same key, use the
-- provided function to decide how to generate the new vertex at the key.
overlayWith :: Ord k => (v -> v -> v) -> Graph k e v -> Graph k e v -> Graph k e v
overlayWith f (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith f v1 v2)
        (M.unionWith (M.unionWith (++)) f1 f2)

-- | Combine two graphs. If both graph have a vertex at the same key, use the
-- vertex label from the first graph.
overlay :: Ord k => Graph k e v -> Graph k e v -> Graph k e v
overlay = overlayWith const

instance Ord k => Monoid (Graph k e v) where
  mempty = empty
  mappend = overlay

instance Ord k => Semigroup (Graph k e v)
instance AsEmpty (Graph k e v) where
  _Empty = nearly empty (\g -> null (g ^. vertMap) && null (g ^. edgeMap))

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
delEdgeBy p k1 k2 g = g & edgeMap . at k1 . _Just . at k2 . _Just %~ filter (not . p)
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
filterVerts p g = foldr (\(k, v) g' -> if not (p v) then delKey k g' else g') g (allLabVerts g)

-- | Filter the edges in the graph by the given predicate.
filterEdges :: Ord k => (e -> Bool) -> Graph k e v -> Graph k e v
filterEdges p g = foldr (\(k1, k2, _) -> delEdgeBy (not . p) k1 k2) g (allLabEdges g)

-- | Filter the keys in the graph by the given predicate.
filterKeys :: Ord k => (k -> Bool) -> Graph k e v -> Graph k e v
filterKeys p g = foldr delKey g (filter (not . p) (keys g))

-- | Remove all empty entries in a map.
cleanup :: (Ord k, Foldable t) => Map k (t a) -> Map k (t a)
cleanup m = foldr clearEntry m (M.keys m)

-- | If the entry at the key in the map is empty, remove that key from the map.
clearEntry :: (Foldable t, Ord k) => k -> Map k (t a) -> Map k (t a)
clearEntry k m = maybe m (\m' -> if null m' then M.delete k m else m) (M.lookup k m)

-- | The map obtained by applying f to each key of s.
-- The size of the result may be smaller if f maps two or more distinct keys to
-- the same new key. In this case the value at the greatest of the original keys
-- is retained.
mapKeys :: Ord k' => (k -> k') -> Graph k e v -> Graph k' e v
mapKeys f (Graph vs fs) =
  Graph (M.mapKeys f vs)
        (M.mapKeys f $ fmap (M.mapKeys f) fs)

-- | Reverse the direction of all edges in the graph.
reverse :: Ord k => Graph k e v -> Graph k e v
reverse g = foldr (\(k1, k2, e) -> addEdge k2 k1 e) init (allLabEdges g)
  where
    init = Graph (g ^. vertMap) M.empty

instance Ord k => Reversing (Graph k e v) where
  reversing = reverse

-- | Decompose the graph into the context about the given key/vertex and
-- the remainder of the graph not in the context.
decompose :: Ord k => k -> v -> Graph k e v -> (Ctxt k e v, Graph k e v)
decompose k v g =
  (Ctxt (labEdgesTo g k) (k, v) (labEdgesFrom g k), delKey k g)

-- | Add the vertex and edges described by the context to the graph. Note that
-- if the context describes edges to/from keys which are not in the graph already
-- then those edges will not be added.
addCtxt :: Ord k => Ctxt k e v -> Graph k e v -> Graph k e v
addCtxt (Ctxt bef (k, v) aft) g =
  foldr (uncurry (k `addEdge`))
    (foldr (uncurry (`addEdge` k)) (addVert k v g) bef)
    aft

-- | A full decomposition of the graph into contexts.
toDecomp :: Ord k => Graph k e v -> [Ctxt k e v]
toDecomp g = fst $ foldr (\(k, v) (cs, g') ->
                                  let (c, g'') = decompose k v g'
                                  in (c : cs, g'')) ([], g) (allLabVerts g)

-- | Construct a graph from a decomposition.
fromDecomp :: Ord k => [Ctxt k e v] -> Graph k e v
fromDecomp = foldl (flip addCtxt) empty

-- | The isomorphism between graphs and their decompositions.
decomp :: (Ord k, Ord k')
       => Iso (Graph k e v) (Graph k' e' v') [Ctxt k e v] [Ctxt k' e' v']
decomp = iso toDecomp fromDecomp

instance (t ~ Graph k' v' e', Ord k) => Rewrapped (Graph k e v) t
instance Ord k => Wrapped (Graph k e v) where
  type Unwrapped (Graph k e v) = [Ctxt k e v]
  _Wrapped' = decomp

instance Functor (Graph k e) where
  fmap f = vertMap %~ fmap f

instance Foldable (Graph k e) where
  foldr f acc g = foldr f acc (g ^. vertMap)

instance Traversable (Graph k e) where
  traverse = traverseOf (vertMap . traverse)

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

-- | Apply the given function to all edges.
mapEdges :: (e -> e') -> Graph k e v -> Graph k e' v
mapEdges = under (from edgeFocused) . fmap

-- | Apply the given function to all vertices, taking each vertex's key as an
-- additional argument.
imapVerts :: (k -> v -> v') -> Graph k e v -> Graph k e v'
imapVerts = imap

-- | Apply the given function to all edges, taking each edge's keys as
-- additional arguments.
imapEdges :: (k -> k -> e -> e') -> Graph k e v -> Graph k e' v
imapEdges = under (from edgeFocused) . imap . uncurry

-- | Aggregate the vertices.
foldVerts :: (v -> b -> b) -> b -> Graph k e v -> b
foldVerts = foldr

-- | Aggregate the edges.
foldEdges :: (e -> b -> b) -> b -> Graph k e v -> b
foldEdges f acc g = foldr f acc (EdgeFocused g)

-- | Aggregate the vertices with vertex keys as an additional argument.
ifoldVerts :: (k -> v -> b -> b) -> b -> Graph k e v -> b
ifoldVerts = ifoldr

-- | Aggregate the edges with edge keys as an additional arguments.
ifoldEdges :: (k -> k -> e -> b -> b) -> b -> Graph k e v -> b
ifoldEdges f acc g = ifoldr (uncurry f) acc (EdgeFocused g)

travVerts :: Applicative f => (v -> f v') -> Graph k e v -> f (Graph k e v')
travVerts = traverse

travEdges :: Applicative f => (e -> f e') -> Graph k e v -> f (Graph k e' v)
travEdges f g = getEdgeFocused <$> traverse f (EdgeFocused g)

itravVerts :: Applicative f => (k -> v -> f v') -> Graph k e v -> f (Graph k e v')
itravVerts = itraverse

itravEdges :: Applicative f => (k -> k -> e -> f e') -> Graph k e v -> f (Graph k e' v)
itravEdges f g = getEdgeFocused <$> itraverse (uncurry f) (EdgeFocused g)

instance Bifunctor (Graph k) where
  bimap fe fv = mapVerts fv . mapEdges fe

-- instance Bifoldable (Graph k) where

dfs :: forall k e v e' v' f. (Ord k, Applicative f) =>
    (e -> f e') -> (v -> f v') -> Graph k e v -> f (Graph k e' v')
dfs fe fv g = evalState dfs' S.empty
  where
    dfs' =

    -- from :: (Applicative f, Ord k) => k -> State (Set k) (f (Graph k e' v'))
    from k = do
      s <- get
      if k `elem` s then undefined
      else do
        modify (S.insert k)
        let es = labEdgesFrom g k
        gs' <- traverse (\(k', e) -> from k') es
        let g' = mconcat <$> sequenceA gs'
        let g'' = case g ^. vert k of
                    Nothing -> g'
                    Just v -> addVert k <$> fv v <*> g'
        return g''
        -- (fmap . fmap) mconcat gs'

test =
  let g1 = addVert 0 "hello" empty
      g2 = addVert 1 "world" g1
      g3 = addVert 2 "sup" g2
      g4 = addEdge 0 1 4.3 g3
      g5 = addEdge 0 1 7.7 g4
      g6 = addEdge 1 0 5.1 g5
      g7 = addEdge 2 0 17.4 g6
      g8 = addEdge 1 2 1.2 g7
  in g8
