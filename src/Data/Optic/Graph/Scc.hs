module Data.Optic.Graph.Scc
  ( scc
  ) where

import Control.Monad.State

import Prelude as P hiding (reverse)

import Data.Optic.Graph.Graph
import Data.Optic.Graph.Traversals
import Data.Optic.Graph.TraversalVariants
import Data.Optic.Graph.Internal.Actions

scc :: Ord i => Graph i e v -> [[i]]
scc = undefined

-- kosajaru :: Ord i => Graph i e v -> [[Action i e v]]
-- kosajaru g =
--   filter (not . null) $ fst $ foldr componentFrom ([], reverse g) (dfsOrder g)
--   where
--     componentFrom :: Ord i => i
--                   -> ([[Action i e v]], Graph i e v)
--                   -> ([[Action i e v]], Graph i e v)
--     componentFrom i (comps, g') =
--       let comp = execState (
--             idfsFrom_ i (\i1 i2 e -> modify (Edge i1 i2 e:))
--                         (\i v -> modify (Vert i v:)) g') []
--       in (comp : comps, filterIdxs (`notElem` actionVIdxs comp) g')

--     actionVIdxs = concatMap (\ac -> case ac of
--       Vert i _ -> [i]
--       Edge{} -> [])
