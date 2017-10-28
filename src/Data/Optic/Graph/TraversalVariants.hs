module Data.Optic.Graph.TraversalVariants
  ( mapVerts, imapVerts
  , mapEdges, imapEdges
  , mapIdxs

  , foldVerts, ifoldVerts
  , foldEdges, ifoldEdges
  , foldIdxs

  , travVerts, itravVerts
  , travEdges, itravEdges
  , travIdxs

  , idfsVert, idfsEdge
  , idfs_, idfsVert_, idfsEdge_
  , dfs, dfsVert, dfsEdge
  , dfs_, dfsVert_, dfsEdge_, dfsIdx_

  , ibfsVert, ibfsEdge
  , ibfs_, ibfsVert_, ibfsEdge_
  , bfs, bfsVert, bfsEdge
  , bfs_, bfsVert_, bfsEdge_, bfsIdx_

  , itopVert, itopEdge
  , itop_, itopVert_, itopEdge_
  , top, topVert, topEdge
  , top_, topVert_, topEdge_, topIdx_

  , idfsFromVert, idfsFromEdge
  , idfsFrom_, idfsFromVert_, idfsFromEdge_
  , dfsFrom, dfsFromVert, dfsFromEdge
  , dfsFrom_, dfsFromVert_, dfsFromEdge_, dfsFromIdx_

  , ibfsFromVert, ibfsFromEdge
  , ibfsFrom_, ibfsFromVert_, ibfsFromEdge_
  , bfsFrom, bfsFromVert, bfsFromEdge
  , bfsFrom_, bfsFromVert_, bfsFromEdge_, bfsFromIdx_

  , ipath, ipathVert, ipathEdge
  , ipath_, ipathVert_, ipathEdge_
  , path, pathVert, pathEdge
  , path_, pathVert_, pathEdge_, pathIdx_

  , reached, reaches
  ) where

import           Control.Lens
import           Control.Monad (void)

import qualified Data.Map as M

import           Data.Optic.Graph.Graph
import           Data.Optic.Graph.EdgeFocused
import           Data.Optic.Graph.Traversals

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
dfsFromIdx_ i fi = void . idfsFromVert i (\i' v -> fi i' *> pure v)
bfsFromIdx_ i fi = void . ibfsFromVert i (\i' v -> fi i' *> pure v)

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
