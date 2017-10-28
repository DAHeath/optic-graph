module Data.Optic.Graph.Scc
  ( scc
  ) where

import Control.Monad.State

import Prelude as P hiding (reverse)

import Data.Optic.Graph.Graph
import Data.Optic.Graph.TraversalVariants

scc :: Ord i => Graph i e v -> [[i]]
scc = kosajaru

kosajaru :: Ord i => Graph i e v -> [[i]]
kosajaru g =
  let l = execState (dfsIdx_ (\i -> modify (i:)) g) []
  in filter (not . null) $ fst $ foldr componentFrom ([], reverse g) l
  where
    componentFrom i (comps, g') =
      let comp = execState (dfsFromIdx_ i (\i' -> modify (i':)) g') []
      in (comp : comps, filterIdxs (`notElem` comp) g)
