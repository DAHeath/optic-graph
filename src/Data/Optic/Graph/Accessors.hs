module Data.Optic.Graph.Accessors
  ( successors, predecessors
  , descendants, ancestors
  , connections
  , order, size
  , elemVert, elemEdge
  ) where

import Control.Lens

import Data.Maybe (mapMaybe)
import Data.List (nub)
import Data.Optic.Graph.Graph
import Data.Optic.Graph.Traversals

import Prelude hiding (reverse)

-- | The successor indices for the given index.
successors :: Ord i => i -> Graph i e v -> [i]
successors i = toListOf $ iedgesFrom i . asIndex

-- | The predecessor indices for the given index.
predecessors :: Ord i => i -> Graph i e v -> [i]
predecessors i = toListOf $ reversed . iedgesFrom i . asIndex

descendants :: Ord i => i -> Graph i e v -> [i]
descendants i g = nub $ map (snd.fst) $ reached i g ^@.. iallEdges

ancestors :: Ord i => i -> Graph i e v -> [i]
ancestors i g = descendants i (reverse g)

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
