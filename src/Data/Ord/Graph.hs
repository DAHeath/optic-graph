{-# LANGUAGE ApplicativeDo
           , TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , RankNTypes
           , LambdaCase
           , TupleSections
           , NoMonomorphismRestriction
           #-}
module Data.Ord.Graph where

import           Control.Lens
import           Control.Monad.State

import           Data.Semigroup
import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S

import           Prelude hiding (reverse)

data Graph k v e = Graph
  { _vertMap :: Map k v
  , _edgeMap :: Map k (Map k [e])
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

data Ctxt k v e = Ctxt
  { _before :: [(k, e)]
  , _here :: (k, v)
  , _after :: [(k, e)]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Ctxt

-- | A lens which selects the vertex at the key (if it exists).
vert :: Ord k => k -> Lens' (Graph k v e) (Maybe v)
vert k = vertMap . at k

-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal' (Graph k v e) v
allVerts = vertMap . traverse

-- | The vertices of the graph, labelled with their keys.
allLabVerts :: Graph k v e -> [(k, v)]
allLabVerts g = M.toList $ g ^. vertMap

-- | A traversal which selects all edges between two keys.
edges :: Ord k => k -> k -> Traversal' (Graph k v e) e
edges k1 k2 = edgeMap . at k1 . _Just . at k2 . _Just . traverse

-- | A traversal which selects all edges that originate at a key.
edgesFrom :: Ord k => k -> Traversal' (Graph k v e) e
edgesFrom k = edgeMap . at k . _Just . traverse . traverse

-- | A traversal which selects all edges in the graph.
allEdges :: Traversal' (Graph k v e) e
allEdges = edgeMap . traverse . traverse . traverse

-- | The edges from the given key, labelled with their target key.
labEdgesFrom :: Ord k => Graph k v e -> k -> [(k, e)]
labEdgesFrom g k = case M.lookup k (g ^. edgeMap) of
  Nothing -> []
  Just m -> concatMap (\(v, es) -> map (v,) es) (M.toList m)

-- | The edges to the given key, labelled with their source key.
labEdgesTo :: Ord k => Graph k v e -> k -> [(k, e)]
labEdgesTo = labEdgesFrom . reverse

-- | All edges in the graph, labelled with their source and target keys.
allLabEdges :: Ord k => Graph k v e -> [(k, k, e)]
allLabEdges g = concatMap (\k1 -> do
    (k2, e) <- labEdgesFrom g k1
    return (k1, k2, e)) (keys g)

-- | Keys of the graph in ascending order.
keys :: Graph k v e -> [k]
keys = M.keys . view vertMap

-- | The set of all keys in the graph.
keysSet :: Graph k v e -> Set k
keysSet = M.keysSet . view vertMap

type instance Index (Graph k v e) = k
type instance IxValue (Graph k v e) = v
instance Ord k => Ixed (Graph k v e)
instance Ord k => At (Graph k v e) where
  at = vert

-- | A graph with no vertices and no edges.
empty :: Graph k v e
empty = Graph M.empty M.empty

-- | Combine two graphs. If both graphs have a vertex at the same key, use the
-- provided function to decide how to generate the new vertex at the key.
overlayWith :: Ord k => (v -> v -> v) -> Graph k v e -> Graph k v e -> Graph k v e
overlayWith f (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith f v1 v2)
        (M.unionWith (M.unionWith (++)) f1 f2)

-- | Combine two graphs. If both graph have a vertex at the same key, use the
-- vertex label from the first graph.
overlay :: Ord k => Graph k v e -> Graph k v e -> Graph k v e
overlay = overlayWith const

instance Ord k => Semigroup (Graph k v e)
instance Ord k => Monoid (Graph k v e) where
  mempty = empty
  mappend = overlay

-- | Add a vertex at the key, or replace the vertex at that key.
addVert :: Ord k => k -> v -> Graph k v e -> Graph k v e
addVert k v g = g & vert k .~ Just v

-- | Add an edge between two keys in the graph if both keys have vertices. If
-- they do not, the graph is unchanged.
addEdge :: Ord k => k -> k -> e -> Graph k v e -> Graph k v e
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
delVert :: (Eq v, Ord k) => v -> Graph k v e -> Graph k v e
delVert v = filterVerts (not . (==) v)

-- | Remove all edges occurring between two keys.
delEdges :: Ord k => k -> k -> Graph k v e -> Graph k v e
delEdges k1 k2 g = g & edgeMap . at k1 . _Just %~ M.delete k2
                     & edgeMap %~ clearEntry k1

-- | Delete any edges between the two keys which satisfy the predicate.
delEdgeBy :: Ord k => (e -> Bool) -> k -> k -> Graph k v e -> Graph k v e
delEdgeBy p k1 k2 g = g & edgeMap . at k1 . _Just . at k2 . _Just %~ filter (not . p)
                        & edgeMap . at k1 . _Just %~ clearEntry k2
                        & edgeMap %~ clearEntry k1

-- | Delete the edge between the two keys with the given value.
delEdge :: (Eq e, Ord k) => k -> k -> e -> Graph k v e -> Graph k v e
delEdge k1 k2 e = delEdgeBy (== e) k1 k2

-- | Remove a key from the graph, deleting the corresponding vertices and
-- edges to and from the key.
delKey :: Ord k => k -> Graph k v e -> Graph k v e
delKey k g = g & vertMap %~ M.delete k
               & edgeMap %~ M.delete k
               & edgeMap . traverse %~ M.delete k
               & edgeMap %~ cleanup

-- | Filter the vertices in the graph by the given predicate.
-- If a vertex is removed, its key and all corresponding edges are also removed.
filterVerts :: Ord k => (v -> Bool) -> Graph k v e -> Graph k v e
filterVerts p g = foldr (\(k, v) g' -> if not (p v) then delKey k g' else g') g (allLabVerts g)

-- | Filter the edges in the graph by the given predicate.
filterEdges :: Ord k => (e -> Bool) -> Graph k v e -> Graph k v e
filterEdges p g = foldr (\(k1, k2, _) -> delEdgeBy (not . p) k1 k2) g (allLabEdges g)

-- | Filter the keys in the graph by the given predicate.
filterKeys :: Ord k => (k -> Bool) -> Graph k v e -> Graph k v e
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
mapKeys :: Ord k' => (k -> k') -> Graph k v e -> Graph k' v e
mapKeys f (Graph vs fs) =
  Graph (M.mapKeys f vs)
        (M.mapKeys f $ fmap (M.mapKeys f) fs)

-- | Reverse the direction of all edges in the graph.
reverse :: Ord k => Graph k v e -> Graph k v e
reverse g = foldr (\(k1, k2, e) -> addEdge k2 k1 e) init (allLabEdges g)
  where
    init = Graph (g ^. vertMap) M.empty

-- | Decompose the graph into the context about the given key/vertex and
-- the remainder of the graph not in the context.
decompose :: Ord k => k -> v -> Graph k v e -> (Ctxt k v e, Graph k v e)
decompose k v g =
  (Ctxt (labEdgesTo g k) (k, v) (labEdgesFrom g k), delKey k g)

-- | A full decomposition of the graph into contexts.
decomposition :: Ord k => Graph k v e -> [Ctxt k v e]
decomposition g = fst $ foldr (\(k, v) (cs, g') ->
                                  let (c, g'') = decompose k v g'
                                  in (c : cs, g'')) ([], g) (allLabVerts g)

dfs :: (Ord k, Applicative f) =>
       (v -> f v') -> (e -> f e') -> Graph k v e -> f (Graph k v' e')
dfs fv fe g = evalState dfs' S.empty
  where
    dfs' = undefined

    from k = do
      s <- get
      if k `elem` s then undefined
      else do
        modify (S.insert k)
        let es = labEdgesFrom k
        traverse

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
