{-|
Module      : Data.Optic.Graph
Description : Directed Graphs with ordered indices.
Copyright   : (c) David Heath, 2017
              License     : BSD3
              Maintainer  : heath.davidanthony@gmail.com
              Stability   : experimental

Directed graphs with arbitrary ordered indices, edge labels, and vertex labels.
The data structure supports a number of traversals and indexed traversals for
manipulating the labels.

The module is intended to be imported qualified, in conjunction with the lens
library.
-}
module Data.Optic.Graph
  ( module Data.Optic.Graph.Graph
  , module Data.Optic.Graph.Accessors
  , module Data.Optic.Graph.EdgeFocused
  , module Data.Optic.Graph.Ctxt
  , module Data.Optic.Graph.Traversals
  , module Data.Optic.Graph.TraversalVariants
  , module Data.Optic.Graph.Scc
  ) where

import Data.Optic.Graph.Graph
import Data.Optic.Graph.Accessors
import Data.Optic.Graph.EdgeFocused
import Data.Optic.Graph.Ctxt
import Data.Optic.Graph.Traversals
import Data.Optic.Graph.TraversalVariants
import Data.Optic.Graph.Scc
