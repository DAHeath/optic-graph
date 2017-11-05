{-# LANGUAGE FlexibleContexts, ViewPatterns, NoMonomorphismRestriction
           , GADTs, ExistentialQuantification, RankNTypes #-}
module Data.Optic.Graph.Traversals
  ( ibitraverse
  , reached, reaches, between

  , mapVert, imapVert
  , mapEdge, imapEdge
  , mapIdx

  , foldVert, ifoldVert
  , foldEdge, ifoldEdge
  , foldIdx

  , travVert, itravVert
  , travEdge, itravEdge
  , travIdx

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

  , idfsTree
  , idfsTreeEdge
  , idfsTree_, idfsTreeEdge_
  , dfsTree, dfsTreeEdge
  , dfsTree_, dfsTreeEdge_

  , ibfsTree
  , ibfsTreeEdge
  , ibfsTree_, ibfsTreeEdge_
  , bfsTree, bfsTreeEdge
  , bfsTree_, bfsTreeEdge_

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

idfsTree, ibfsTree :: (Applicative f, Ord i)
                   => (i -> i -> e -> f e)
                   -> (i -> v -> f v)
                   -> Graph i e v -> f (Graph i e v)
idfsTree fe fv g = actionsToGraph fe fv $ treeActions $ evalState (dfs' g) S.empty
ibfsTree fe fv g = actionsToGraph fe fv $ treeActions $ evalState (bfs' g) S.empty

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

treeActions :: Eq i => [Action i e v] -> [Action i e v]
treeActions (Edge{} : Edge i1 i2 e : acs) = treeActions (Edge i1 i2 e : acs)
treeActions (ac : acs) = ac : treeActions acs
treeActions [] = []

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
mapVert :: (v -> v') -> Graph i e v -> Graph i e v'
mapVert = fmap

-- | Apply the given function to all vertices, taking each vertex's index as an
-- additional argument.
imapVert :: (i -> v -> v') -> Graph i e v -> Graph i e v'
imapVert = imap

-- | Apply the given function to all edges.
mapEdge :: (e -> e') -> Graph i e v -> Graph i e' v
mapEdge = under (from edgeFocused) . fmap

-- | Apply the given function to all edges, taking each edge's indices as
-- additional arguments.
imapEdge :: (i -> i -> e -> e') -> Graph i e v -> Graph i e' v
imapEdge = under (from edgeFocused) . imap . uncurry

-- | The map obtained by applying f to each index of s.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
mapIdx :: Ord i' => (i -> i') -> Graph i e v -> Graph i' e v
mapIdx f (Graph vs es) =
  Graph (M.mapKeys f vs)
        (M.mapKeys f $ fmap (M.mapKeys f) es)

-- | Aggregate the vertices.
foldVert :: (v -> b -> b) -> b -> Graph i e v -> b
foldVert = foldr

-- | Aggregate the vertices with the vertex index as an additional argument.
ifoldVert :: (i -> v -> b -> b) -> b -> Graph i e v -> b
ifoldVert = ifoldr

-- | Aggregate the edges.
foldEdge :: (e -> b -> b) -> b -> Graph i e v -> b
foldEdge f acc g = foldr f acc (EdgeFocused g)

-- | Aggregate the edges with the edge indices as additional arguments.
ifoldEdge :: (i -> i -> e -> b -> b) -> b -> Graph i e v -> b
ifoldEdge f acc g = ifoldr (uncurry f) acc (EdgeFocused g)

-- | Aggregate the indices.
foldIdx :: (i -> b -> b) -> b -> Graph i e v -> b
foldIdx f acc g = foldr f acc (idxs g)

-- | Traverse the vertices.
travVert :: Applicative f => (v -> f v') -> Graph i e v -> f (Graph i e v')
travVert = traverse

-- | Indexed vertex traversal.
itravVert :: Applicative f => (i -> v -> f v') -> Graph i e v -> f (Graph i e v')
itravVert = itraverse

-- | Traverse the edges.
travEdge :: Applicative f => (e -> f e') -> Graph i e v -> f (Graph i e' v)
travEdge = allEdges

-- | Indexed edge traversal.
itravEdge :: Applicative f => (i -> i -> e -> f e') -> Graph i e v -> f (Graph i e' v)
itravEdge f g = getEdgeFocused <$> itraverse (uncurry f) (EdgeFocused g)

-- | Traverse the indices.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
travIdx :: (Applicative f, Ord i, Ord i') => (i -> f i') -> Graph i e v -> f (Graph i' e v)
travIdx f g =
  replace (idxs g) <$> traverse f (idxs g)
  where
    replace is is' =
      let m = M.fromList (zip is is')
      in mapIdx (\i -> m M.! i) g

data Trav g f i e e' v v' = Trav
  { getitrav :: (i -> i -> e -> f e')
             -> (i -> v -> f v')
             -> Graph i e v -> g (f (Graph i e' v'))
  , getitravVert :: (e' ~ e)
                 => (i -> v -> f v')
                 -> Graph i e v -> g (f (Graph i e v'))
  , getitravEdge :: (v' ~ v)
                 => (i -> i -> e -> f e')
                 -> Graph i e v -> g (f (Graph i e' v))
  , getitrav_ :: forall e'' v''. (e' ~ e, v' ~ v)
              => (i -> i -> e -> f e'')
              -> (i -> v -> f v'')
              -> Graph i e v -> g (f ())
  , getitravVert_ :: forall v''. (e' ~ e, v' ~ v)
                  => (i -> v -> f v'')
                  -> Graph i e v -> g (f ())
  , getitravEdge_ :: forall e'' v''. (e' ~ e, v' ~ v)
                  => (i -> i -> e -> f e'')
                  -> Graph i e v -> g (f ())
  , gettrav :: (e -> f e')
            -> (v -> f v')
            -> Graph i e v -> g (f (Graph i e' v'))
  , gettravVert :: (e' ~ e)
                => (v -> f v')
                -> Graph i e v -> g (f (Graph i e' v'))
  , gettravEdge :: (v' ~ v)
                => (e -> f e')
                -> Graph i e v -> g (f (Graph i e' v'))
  , gettrav_ :: forall e'' v''. (e' ~ e, v' ~ v)
             => (e -> f e'')
             -> (v -> f v'')
             -> Graph i e v -> g (f ())
  , gettravVert_ :: forall v''. (e' ~ e, v' ~ v)
                 => (v -> f v'')
                 -> Graph i e v -> g (f ())
  , gettravEdge_ :: forall e''. (e' ~ e, v' ~ v)
                 => (e -> f e'')
                 -> Graph i e v -> g (f ())
  , gettravIdx_ :: forall i'. (e' ~ e, v' ~ v)
                => (i -> f i')
                -> Graph i e v -> g (f ())
  , gettravIdxs :: (e' ~ e, v' ~ v, f ~ State [i]) => Graph i e v -> g [i]
  }

mkTrav :: (Functor g, Applicative f, Ord i)
       => ((i -> i -> e -> f e')
           -> (i -> v -> f v')
           -> Graph i e v -> g (f (Graph i e' v')))
       -> Trav g f i e e' v v'
mkTrav itrav =
  let theTrav = Trav
        { getitrav = itrav
        , getitravVert = itrav (\_ _ -> pure)
        , getitravEdge = \fe -> itrav fe (const pure)
        , getitrav_ = \fe fv -> fmap void . itrav (\i1 i2 e -> fe i1 i2 e *> pure e)
                                               (\i v -> fv i v *> pure v)
        , getitravVert_ = getitrav_ theTrav (\_ _ _ -> pure ())
        , getitravEdge_ = \fe -> getitrav_ theTrav fe (\_ _ -> pure ())
        , gettrav = \fe fv -> itrav (\_ _ -> fe) (const fv)
        , gettravVert = gettrav theTrav pure
        , gettravEdge = \fe -> gettrav theTrav fe pure
        , gettrav_ = \fe fv -> fmap void . gettrav theTrav (\e -> fe e *> pure e)
                                                     (\v -> fv v *> pure v)
        , gettravVert_ = gettrav_ theTrav (\_ -> pure ())
        , gettravEdge_ = \fe -> gettrav_ theTrav fe (\_ -> pure ())
        , gettravIdx_ = \fi -> getitravVert_ theTrav (\i _ -> fi i)
        , gettravIdxs =
            fmap (\ac -> reversing $ execState ac []) . gettravIdx_ theTrav (\i -> modify (i:))
        }
  in theTrav

dfsTravs, bfsTravs :: (Applicative f, Ord i) => Trav Identity f i e e' v v'
dfsTravs = mkTrav (\fe fv -> Identity . idfs fe fv)
bfsTravs = mkTrav (\fe fv -> Identity . ibfs fe fv)

dfsTreeTravs, bfsTreeTravs :: (Applicative f, Ord i, e' ~ e, v' ~ v)
                           => Trav Identity f i e e' v v'
dfsTreeTravs = mkTrav (\fe fv -> Identity . idfsTree fe fv)
bfsTreeTravs = mkTrav (\fe fv -> Identity . ibfsTree fe fv)


dfsFromTravs, bfsFromTravs :: (Applicative f, Ord i, e' ~ e, v' ~ v)
                             => i -> Trav Identity f i e e' v v'
dfsFromTravs i = mkTrav (\fe fv -> Identity . idfsFrom i fe fv)
bfsFromTravs i = mkTrav (\fe fv -> Identity . ibfsFrom i fe fv)

topTravs :: (Applicative f, Ord i) => Trav Maybe f i e e' v v'
topTravs = mkTrav itop

pathTravs :: (Applicative f, Ord i, e' ~ e, v' ~ v) => i -> i -> Trav Maybe f i e e' v v'
pathTravs i1 i2 = mkTrav (ipath i1 i2)

sccTravs :: (Applicative f, Ord i, e' ~ e, v' ~ v) => Trav [] f i e e' v v'
sccTravs = mkTrav iscc

idfsVert fv  = runIdentity . getitravVert dfsTravs fv
idfsEdge fe  = runIdentity . getitravEdge dfsTravs fe
idfs_ fe fv  = runIdentity . getitrav_ dfsTravs fe fv
idfsVert_ fv = runIdentity . getitravVert_ dfsTravs fv
idfsEdge_ fe = runIdentity . getitravEdge_ dfsTravs fe
dfs fe fv    = runIdentity . gettrav dfsTravs fe fv
dfsVert fv   = runIdentity . gettravVert dfsTravs fv
dfsEdge fe   = runIdentity . gettravEdge dfsTravs fe
dfs_ fe fv   = runIdentity . gettrav_ dfsTravs fe fv
dfsVert_ fv  = runIdentity . gettravVert_ dfsTravs fv
dfsEdge_ fe  = runIdentity . gettravEdge_ dfsTravs fe
dfsIdx_ fi   = runIdentity . gettravIdx_ dfsTravs fi
dfsIdxs      = runIdentity . gettravIdxs dfsTravs

ibfsVert fv  = runIdentity . getitravVert bfsTravs fv
ibfsEdge fe  = runIdentity . getitravEdge bfsTravs fe
ibfs_ fe fv  = runIdentity . getitrav_ bfsTravs fe fv
ibfsVert_ fv = runIdentity . getitravVert_ bfsTravs fv
ibfsEdge_ fe = runIdentity . getitravEdge_ bfsTravs fe
bfs fe fv    = runIdentity . gettrav bfsTravs fe fv
bfsVert fv   = runIdentity . gettravVert bfsTravs fv
bfsEdge fe   = runIdentity . gettravEdge dfsTravs fe
bfs_ fe fv   = runIdentity . gettrav_ bfsTravs fe fv
bfsVert_ fv  = runIdentity . gettravVert_ bfsTravs fv
bfsEdge_ fe  = runIdentity . gettravEdge_ bfsTravs fe
bfsIdx_ fi   = runIdentity . gettravIdx_ bfsTravs fi
bfsIdxs      = runIdentity . gettravIdxs bfsTravs

idfsTreeEdge fe  = runIdentity . getitravEdge dfsTreeTravs fe
idfsTree_ fe fv  = runIdentity . getitrav_ dfsTreeTravs fe fv
idfsTreeEdge_ fe = runIdentity . getitravEdge_ dfsTreeTravs fe
dfsTree fe fv    = runIdentity . gettrav dfsTreeTravs fe fv
dfsTreeEdge fe   = runIdentity . gettravEdge dfsTreeTravs fe
dfsTree_ fe fv   = runIdentity . gettrav_ dfsTreeTravs fe fv
dfsTreeEdge_ fe  = runIdentity . gettravEdge_ dfsTreeTravs fe

ibfsTreeEdge fe  = runIdentity . getitravEdge bfsTreeTravs fe
ibfsTree_ fe fv  = runIdentity . getitrav_ bfsTreeTravs fe fv
ibfsTreeEdge_ fe = runIdentity . getitravEdge_ bfsTreeTravs fe
bfsTree fe fv    = runIdentity . gettrav bfsTreeTravs fe fv
bfsTreeEdge fe   = runIdentity . gettravEdge dfsTreeTravs fe
bfsTree_ fe fv   = runIdentity . gettrav_ bfsTreeTravs fe fv
bfsTreeEdge_ fe  = runIdentity . gettravEdge_ bfsTreeTravs fe

idfsFromVert i fv  = runIdentity . getitravVert (dfsFromTravs i) fv
idfsFromEdge i fe  = runIdentity . getitravEdge (dfsFromTravs i) fe
idfsFrom_ i fe fv  = runIdentity . getitrav_ (dfsFromTravs i) fe fv
idfsFromVert_ i fv = runIdentity . getitravVert_ (dfsFromTravs i) fv
idfsFromEdge_ i fe = runIdentity . getitravEdge_ (dfsFromTravs i) fe
dfsFrom i fe fv    = runIdentity . gettrav (dfsFromTravs i) fe fv
dfsFromVert i fv   = runIdentity . gettravVert (dfsFromTravs i) fv
dfsFromEdge i fe   = runIdentity . gettravEdge (dfsFromTravs i) fe
dfsFrom_ i fe fv   = runIdentity . gettrav_ (dfsFromTravs i) fe fv
dfsFromVert_ i fv  = runIdentity . gettravVert_ (dfsFromTravs i) fv
dfsFromEdge_ i fe  = runIdentity . gettravEdge_ (dfsFromTravs i) fe
dfsFromIdx_ i fi   = runIdentity . gettravIdx_ (dfsFromTravs i) fi
dfsFromIdxs i      = runIdentity . gettravIdxs (dfsFromTravs i)

ibfsFromVert i fv  = runIdentity . getitravVert (bfsFromTravs i) fv
ibfsFromEdge i fe  = runIdentity . getitravEdge (bfsFromTravs i) fe
ibfsFrom_ i fe fv  = runIdentity . getitrav_ (bfsFromTravs i) fe fv
ibfsFromVert_ i fv = runIdentity . getitravVert_ (bfsFromTravs i) fv
ibfsFromEdge_ i fe = runIdentity . getitravEdge_ (bfsFromTravs i) fe
bfsFrom i fe fv    = runIdentity . gettrav (bfsFromTravs i) fe fv
bfsFromVert i fv   = runIdentity . gettravVert (bfsFromTravs i) fv
bfsFromEdge i fe   = runIdentity . gettravEdge (bfsFromTravs i) fe
bfsFrom_ i fe fv   = runIdentity . gettrav_ (bfsFromTravs i) fe fv
bfsFromVert_ i fv  = runIdentity . gettravVert_ (bfsFromTravs i) fv
bfsFromEdge_ i fe  = runIdentity . gettravEdge_ (bfsFromTravs i) fe
bfsFromIdx_ i fi   = runIdentity . gettravIdx_ (bfsFromTravs i) fi
bfsFromIdxs i      = runIdentity . gettravIdxs (bfsFromTravs i)

itopVert  = getitravVert topTravs
itopEdge  = getitravEdge topTravs
itop_     = getitrav_ topTravs
itopVert_ = getitravVert_ topTravs
itopEdge_ = getitravEdge_ topTravs
top       = gettrav topTravs
topVert   = gettravVert topTravs
topEdge   = gettravEdge dfsTravs
top_      = gettrav_ topTravs
topVert_  = gettravVert_ topTravs
topEdge_  = gettravEdge_ topTravs
topIdx_   = gettravIdx_ topTravs
topIdxs   = gettravIdxs topTravs

ipathVert  i1 i2 = getitravVert (pathTravs i1 i2)
ipathEdge  i1 i2 = getitravEdge (pathTravs i1 i2)
ipath_     i1 i2 = getitrav_ (pathTravs i1 i2)
ipathVert_ i1 i2 = getitravVert_ (pathTravs i1 i2)
ipathEdge_ i1 i2 = getitravEdge_ (pathTravs i1 i2)
path       i1 i2 = gettrav (pathTravs i1 i2)
pathVert   i1 i2 = gettravVert (pathTravs i1 i2)
pathEdge   i1 i2 = gettravEdge dfsTravs
path_      i1 i2 = gettrav_ (pathTravs i1 i2)
pathVert_  i1 i2 = gettravVert_ (pathTravs i1 i2)
pathEdge_  i1 i2 = gettravEdge_ (pathTravs i1 i2)
pathIdx_   i1 i2 = gettravIdx_ (pathTravs i1 i2)
pathIdxs   i1 i2 = gettravIdxs (pathTravs i1 i2)

isccVert  = getitravVert sccTravs
isccEdge  = getitravEdge sccTravs
iscc_     = getitrav_ sccTravs
isccVert_ = getitravVert_ sccTravs
isccEdge_ = getitravEdge_ sccTravs
scc       = gettrav sccTravs
sccVert   = gettravVert sccTravs
sccEdge   = gettravEdge dfsTravs
scc_      = gettrav_ sccTravs
sccVert_  = gettravVert_ sccTravs
sccEdge_  = gettravEdge_ sccTravs
sccIdx_   = gettravIdx_ sccTravs
sccIdxs   = gettravIdxs sccTravs
