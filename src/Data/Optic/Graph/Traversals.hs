{-# LANGUAGE FlexibleContexts, ViewPatterns, NoMonomorphismRestriction #-}
module Data.Optic.Graph.Traversals
  ( ibitraverse

  , idfs, ibfs, itop
  , idfsFrom, ibfsFrom
  , ipath

  , reached, reaches, between
  ) where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Loops (whileM, whileM_)

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import           Data.List (minimumBy)
import           Data.Maybe (maybeToList)
import           Data.Foldable (fold)

import           Prelude as P hiding (reverse)

import           Data.Optic.Graph.Graph
import           Data.Optic.Graph.Internal.Actions

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
      g'' = foldr (\((i1, i2), _) -> delEdge i1 i2) g es
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
  theSet <~ uses graph noIncoming
  acs <- fmap concat $ whileM (uses theSet $ not . null) $ do
    i <- zoom theSet $ state S.deleteFindMin
    g <- use graph
    v <- lift $ g ^. at i
    fmap (Vert i v:) $ forM (g ^@.. iedgesFrom i) $ \(i', e) -> do
      g' <- graph <%= delEdge i i'
      when (hasn't (edgesTo i') g') (theSet %= S.insert i')
      return $ Edge i i' e
  guard =<< uses graph (nullOf allEdges)
  return acs
  where
    hasIncoming g = S.fromList $ map (snd . fst) $ g ^@.. iallEdges
    noIncoming g = idxSet g `S.difference` hasIncoming g
    theSet = _1
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
  m <- dijkstra' (const (1 :: Integer)) i1 g
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

-- | The subgraph reached from the given index.
reached :: Ord i => i -> Graph i e v -> Graph i e v
reached i = runIdentity . travActs (\_ _ e -> Identity e) (\_ v -> Identity v) (dfsFrom' i)

-- | The subgraph that reaches the given index.
reaches :: Ord i => i -> Graph i e v -> Graph i e v
reaches i = reverse . reached i . reverse

-- | Find the subgraph occurring between the two indices.
between :: Ord i => i -> i -> Graph i e v -> Graph i e v
between i1 i2 g =
  let is1 = idxSet (reached i1 g)
      is2 = idxSet (reaches i2 g)
      is = S.intersection is1 is2
  in filterIdxs (`elem` is) g

-- | Dijkstra/Bellman Ford shortest path from the given index. The result is a map
-- of the index to the information required to reconstruct the path the index's
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
      ds' <- use dists
      let alt = (+ weight e) <$> M.lookup near ds'
      when (cmp alt (M.lookup i' ds') == LT) $ do
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
