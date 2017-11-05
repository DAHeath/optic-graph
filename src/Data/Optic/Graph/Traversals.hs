{-# LANGUAGE FlexibleContexts, ViewPatterns, NoMonomorphismRestriction #-}
module Data.Optic.Graph.Traversals
  ( ibitraverse
  , reached, reaches, between

  , mapVerts, imapVerts
  , mapEdges, imapEdges
  , mapIdxs

  , foldVerts, ifoldVerts
  , foldEdges, ifoldEdges
  , foldIdxs

  , travVerts, itravVerts
  , travEdges, itravEdges
  , travIdxs

  , idfs
  , idfsVert, idfsEdge
  , idfs_, idfsVert_, idfsEdge_
  , dfs, dfsVert, dfsEdge
  , dfs_, dfsVert_, dfsEdge_, dfsIdx_
  , dfsIdxs

  , ibfs
  , ibfsVert, ibfsEdge
  , ibfs_, ibfsVert_, ibfsEdge_
  , bfs, bfsVert, bfsEdge
  , bfs_, bfsVert_, bfsEdge_, bfsIdx_
  , bfsIdxs

  , itop
  , itopVert, itopEdge
  , itop_, itopVert_, itopEdge_
  , top, topVert, topEdge
  , top_, topVert_, topEdge_, topIdx_
  , topIdxs

  , idfsFrom
  , idfsFromVert, idfsFromEdge
  , idfsFrom_, idfsFromVert_, idfsFromEdge_
  , dfsFrom, dfsFromVert, dfsFromEdge
  , dfsFrom_, dfsFromVert_, dfsFromEdge_, dfsFromIdx_
  , dfsFromIdxs

  , ibfsFrom
  , ibfsFromVert, ibfsFromEdge
  , ibfsFrom_, ibfsFromVert_, ibfsFromEdge_
  , bfsFrom, bfsFromVert, bfsFromEdge
  , bfsFrom_, bfsFromVert_, bfsFromEdge_, bfsFromIdx_
  , bfsFromIdxs

  , ipath
  , ipathVert, ipathEdge
  , ipath_, ipathVert_, ipathEdge_
  , path, pathVert, pathEdge
  , path_, pathVert_, pathEdge_, pathIdx_
  , pathIdxs

  , iscc
  , isccVert, isccEdge
  , iscc_, isccVert_, isccEdge_
  , scc, sccVert, sccEdge
  , scc_, sccVert_, sccEdge_, sccIdx_
  , sccIdxs
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
import           Data.Optic.Graph.EdgeFocused
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
  in union <$> g' <*> pure g
ibfsFrom i fe fv g =
  let g' = travActs fe fv (bfsFrom' i) g
  in union <$> g' <*> pure g

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
  return (union <$> g' <*> pure g)
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

iscc :: (Applicative f, Ord i)
     => (i -> i -> e -> f e)
     -> (i -> v -> f v)
     -> Graph i e v -> [f (Graph i e v)]
iscc fe fv g =
  map (\acs ->
    let g' = actionsToGraph fe fv (reversing acs)
    in union <$> g' <*> pure g) (kosajaru g)

kosajaru :: Ord i => Graph i e v -> [[Action i e v]]
kosajaru g =
  filter (not . null) $ fst $ foldr componentFrom ([], reverse g) (reversing $ dfsIdxs g)
  where
    componentFrom :: Ord i => i
                  -> ([[Action i e v]], Graph i e v)
                  -> ([[Action i e v]], Graph i e v)
    componentFrom i (comps, g') =
      let comp = execState (
            idfsFrom_ i (\i1 i2 e -> modify (Edge i1 i2 e:))
                        (\i' v -> modify (Vert i' v:)) g') []
      in (comp : comps, filterIdxs (`notElem` actionVIdxs comp) g')

    actionVIdxs = concatMap (\ac -> case ac of
      Vert i _ -> [i]
      Edge{} -> [])


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

dfsIdxs, bfsIdxs :: Ord i => Graph i e v -> [i]
dfsIdxs g = reversing $ execState (dfsIdx_ (\i -> modify (i:)) g) []
bfsIdxs g = reversing $ execState (bfsIdx_ (\i -> modify (i:)) g) []

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

topIdxs :: Ord i => Graph i e v -> Maybe [i]
topIdxs g = reversing <$> (execState <$> topIdx_ (\i -> modify (i:)) g <*> pure [])

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
                     => i -> (i -> i -> e -> f e') -> (i -> v -> f v') -> Graph i e v -> f ()
idfsFrom_ i fe fv = void . idfsFrom i (\i1 i2 e -> fe i1 i2 e *> pure e)
                                      (\i' v -> fv i' v *> pure v)
ibfsFrom_ i fe fv = void . ibfsFrom i (\i1 i2 e -> fe i1 i2 e *> pure e)
                                      (\i' v -> fv i' v *> pure v)

idfsFromVert_, ibfsFromVert_ :: (Applicative f, Ord i)
                             => i -> (i -> v -> f v') -> Graph i e v -> f ()
idfsFromVert_ i fv = void . idfsFromVert i (\i' v -> fv i' v *> pure v)
ibfsFromVert_ i fv = void . ibfsFromVert i (\i' v -> fv i' v *> pure v)

idfsFromEdge_, ibfsFromEdge_ :: (Applicative f, Ord i)
                             => i -> (i -> i -> e -> f e') -> Graph i e v -> f ()
idfsFromEdge_ i fe = void . idfsFromEdge i (\i1 i2 e -> fe i1 i2 e *> pure e)
ibfsFromEdge_ i fe = void . ibfsFromEdge i (\i1 i2 e -> fe i1 i2 e *> pure e)

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
                   => i -> (e -> f e') -> (v -> f v') -> Graph i e v -> f ()
dfsFrom_ i fe fv = void . dfsFrom i (\e -> fe e *> pure e) (\v -> fv v *> pure v)
bfsFrom_ i fe fv = void . bfsFrom i (\e -> fe e *> pure e) (\v -> fv v *> pure v)

dfsFromVert_, bfsFromVert_ :: (Ord i, Applicative f)
                   => i -> (v -> f v') -> Graph i e v -> f ()
dfsFromVert_ i fv = void . dfsFromVert i (\v -> fv v *> pure v)
bfsFromVert_ i fv = void . bfsFromVert i (\v -> fv v *> pure v)

dfsFromEdge_, bfsFromEdge_ :: (Ord i, Applicative f)
                           => i -> (e -> f e') -> Graph i e v -> f ()
dfsFromEdge_ i fe = void . dfsFromEdge i (\e -> fe e *> pure e)
bfsFromEdge_ i fe = void . bfsFromEdge i (\e -> fe e *> pure e)

dfsFromIdx_, bfsFromIdx_ :: (Applicative f, Ord i)
                         => i -> (i -> f i') -> Graph i e v -> f ()
dfsFromIdx_ i fi = void . idfsFromVert i (\i' v -> fi i' *> pure v)
bfsFromIdx_ i fi = void . ibfsFromVert i (\i' v -> fi i' *> pure v)

dfsFromIdxs, bfsFromIdxs :: Ord i => i -> Graph i e v -> [i]
dfsFromIdxs i g = reversing $ execState (dfsFromIdx_ i (\i' -> modify (i':)) g) []
bfsFromIdxs i g = reversing $ execState (bfsFromIdx_ i (\i' -> modify (i':)) g) []

-- | Path traversals

ipathVert :: (Ord i, Applicative f)
          => i -> i -> (i -> v -> f v) -> Graph i e v -> Maybe (f (Graph i e v))
ipathVert i1 i2 = ipath i1 i2 (\_ _ -> pure)

ipathEdge :: (Ord i, Applicative f)
          => i -> i -> (i -> i -> e -> f e) -> Graph i e v -> Maybe (f (Graph i e v))
ipathEdge i1 i2 fe = ipath i1 i2 fe (const pure)

ipath_ :: (Ord i, Applicative f)
       => i -> i -> (i -> i -> e -> f e') -> (i -> v -> f v') -> Graph i e v -> Maybe (f ())
ipath_ i1 i2 fe fv g = void <$> ipath i1 i2
  (\i1' i2' e -> fe i1' i2' e *> pure e)
  (\i v -> fv i v *> pure v) g

ipathVert_ :: (Applicative f, Ord i)
           => i -> i -> (i -> v -> f v') -> Graph i e v -> Maybe (f ())
ipathVert_ i1 i2 fv g = void <$> ipathVert i1 i2 (\i v -> fv i v *> pure v) g

ipathEdge_ :: (Applicative f, Ord i)
           => i -> i -> (i -> i -> e -> f e') -> Graph i e v -> Maybe (f ())
ipathEdge_ i1 i2 fe g = void <$> ipathEdge i1 i2 (\i1' i2' e -> fe i1' i2' e *> pure e) g

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
      => i -> i -> (e -> f e') -> (v -> f v') -> Graph i e v -> Maybe (f ())
path_ i1 i2 fe fv g = void <$> path i1 i2 (\e -> fe e *> pure e)
                                          (\v -> fv v *> pure v) g

pathVert_ :: (Ord i, Applicative f)
          => i -> i -> (v -> f v') -> Graph i e v -> Maybe (f ())
pathVert_ i1 i2 fv g = void <$> pathVert i1 i2 (\v -> fv v *> pure v) g

pathEdge_ :: (Ord i, Applicative f)
         => i -> i -> (e -> f e') -> Graph i e v -> Maybe (f ())
pathEdge_ i1 i2 fe g = void <$> pathEdge i1 i2 (\e -> fe e *> pure e) g

pathIdx_ :: (Applicative f, Ord i)
         => i -> i -> (i -> f i') -> Graph i e v -> Maybe (f ())
pathIdx_ i1 i2 fi g = void <$> ipathVert i1 i2 (\i v -> fi i *> pure v) g

pathIdxs :: Ord i => i -> i -> Graph i e v -> Maybe [i]
pathIdxs i1 i2 g =
  fmap (\ac -> reversing $ execState ac []) (pathIdx_ i1 i2 (\i -> modify (i:)) g)

-- | Multi, partial traversals

isccVert :: (Applicative f, Ord i)
         => (i -> v -> f v) -> Graph i e v -> [f (Graph i e v)]
isccVert = iscc (\_ _ -> pure)

isccEdge :: (Applicative f, Ord i)
         => (i -> i -> e -> f e) -> Graph i e v -> [f (Graph i e v)]
isccEdge fe = iscc fe (const pure)

iscc_ :: (Applicative f, Ord i)
      => (i -> i -> e -> f e')
      -> (i -> v -> f v')
      -> Graph i e v -> [f ()]
iscc_ fe fv = map void . iscc (\i1 i2 e -> fe i1 i2 e *> pure e)
                              (\i v -> fv i v *> pure v)

isccVert_ :: (Applicative f, Ord i)
          => (i -> v -> f v')
          -> Graph i e v -> [f ()]
isccVert_ = iscc_ (\_ _ _ -> pure ())

isccEdge_ :: (Applicative f, Ord i)
          => (i -> i -> e -> f e')
          -> Graph i e v -> [f ()]
isccEdge_ fe = iscc_ fe (\_ _ -> pure ())

scc :: (Applicative f, Ord i)
    => (e -> f e)
    -> (v -> f v)
    -> Graph i e v -> [f (Graph i e v)]
scc fe fv = iscc (\_ _ -> fe) (const fv)

sccVert :: (Applicative f, Ord i) => (v -> f v) -> Graph i e v -> [f (Graph i e v)]
sccVert = scc pure

sccEdge :: (Applicative f, Ord i) => (e -> f e) -> Graph i e v -> [f (Graph i e v)]
sccEdge fe = scc fe pure

scc_ :: (Applicative f, Ord i)
     => (e -> f e')
     -> (v -> f v')
     -> Graph i e v -> [f ()]
scc_ fe fv = map void . scc (\e -> fe e *> pure e) (\v -> fv v *> pure v)

sccVert_ :: (Applicative f, Ord i) => (v -> f v') -> Graph i e v -> [f ()]
sccVert_ = scc_ (\_ -> pure ())

sccEdge_ :: (Applicative f, Ord i) => (e -> f e') -> Graph i e v -> [f ()]
sccEdge_ fe = scc_ fe (\_ -> pure ())

sccIdx_ :: (Applicative f, Ord i) => (i -> f i') -> Graph i e v -> [f ()]
sccIdx_ fi = isccVert_ (\i _ -> fi i)

sccIdxs :: Ord i => Graph i e v -> [[i]]
sccIdxs g = map (\ac -> reversing $ execState ac []) (sccIdx_ (\i -> modify (i:)) g)
