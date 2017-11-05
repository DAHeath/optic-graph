module Main where

import           Control.Lens

import           Data.Bifunctor (bimap)
import           Data.Maybe (fromMaybe)
import           Data.Optic.Graph

-- | In this example, we will show how a partial traversal allows targetting of
-- a portion of the graph.
--
-- Specifically, we will use the `path` traversal to create a `graphviz` file which
-- displays vertices and edges in bold if they occur on the path between two
-- selected vertices.

-- | This is an example graph with no labels.
example :: Graph Int () ()
example = fromLists
  (zip [0..5] (repeat ()))
  [ (0, 1, ())
  , (0, 2, ())
  , (0, 5, ())
  , (1, 2, ())
  , (1, 3, ())
  , (2, 3, ())
  , (2, 5, ())
  , (3, 4, ())
  , (4, 5, ())
  ]

-- | Our convention will be that the edges/vertices will be labelled with a Boolean
-- value indicating whether or not they should be set if bold.
-- `highlightPath` sets all labels to `False` before flipping those labels on the
-- path to true.
highlightPath :: Ord i => i -> i -> Graph i e v -> Graph i Bool Bool
highlightPath i1 i2 g =
  let g' = bimap (const False) (const False) g
  in runIdentity $ fromMaybe (return g') (path i1 i2 (\_ -> return True) (\_ -> return True) g')

-- | Writing a dot file from the labelled graph is now straightforward.
toDot :: Graph Int Bool Bool -> String
toDot g =
  unlines (["digraph {"]                  -- graphviz header
        ++ map dotVert (g ^@.. iallVerts) -- vertices with optional styling
        ++ map dotEdge (g ^@.. iallEdges) -- edges with optional styling
        ++ ["}"])                         -- graphviz footer
  where
    -- bold style string or empty string depending on boolean value.
    boldOn b = if b then " [style=\"bold\"]" else ""
    -- vertex with optional bold styling
    dotVert (i, v) = show i ++ boldOn v
    -- edge with optional bold styling
    dotEdge ((i1, i2), e) = show i1 ++ " -> " ++ show i2 ++ boldOn e

-- | Write out the generated dot string for our example.
main :: IO ()
main = putStr $ toDot (highlightPath 0 4 example)
