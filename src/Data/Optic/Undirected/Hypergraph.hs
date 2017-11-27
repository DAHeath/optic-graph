module Data.Optic.Undirected.HyperGraph
  ( Graph
  , module Data.Optic.Internal.Graph
  ) where

import           Data.Set (Set)
import qualified Data.Optic.Internal.Graph as I
import           Data.Optic.Internal.Graph hiding (Graph)

type Graph i e v = I.Graph Set i e v
