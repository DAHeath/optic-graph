{-# LANGUAGE DeriveDataTypeable
           , FlexibleInstances
           , MultiParamTypeClasses
           , TypeFamilies
           , UndecidableInstances
           #-}
module Data.Optic.Graph.EdgeFocused
  ( EdgeFocused(..), edgeFocused
  ) where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Data.Optic.Graph.Graph

-- | By default, graphs are "focused" on the vertices, meaning that common
-- typeclass instances act on the vertices. EdgeFocused provides an alternative
-- representation where the edges are the focus of the typeclasses.
newtype EdgeFocused i v e = EdgeFocused { getEdgeFocused :: Graph i e v }
  deriving (Show, Read, Eq, Ord, Data)

-- | Isomorphism between the graph and its edge focused equivalent.
edgeFocused :: Iso (Graph i e v) (Graph i' e' v')
                   (EdgeFocused i v e) (EdgeFocused i' v' e')
edgeFocused = iso EdgeFocused getEdgeFocused

instance Ord i => Functor (EdgeFocused i v) where
  fmap = over (from edgeFocused . edgeMap) . fmap . fmap

instance Foldable (EdgeFocused i v) where
  foldr = foldrOf (from edgeFocused . allEdges)

instance Ord i => Traversable (EdgeFocused i v) where
  traverse = traverseOf (from edgeFocused . allEdges)

instance (Ord i, i ~ i', v ~ v')
  => Each (EdgeFocused i v e) (EdgeFocused i' v' e') e e' where
  each = traversed

instance Ord i => FunctorWithIndex (i, i) (EdgeFocused i v)
instance Ord i => FoldableWithIndex (i, i) (EdgeFocused i v)
instance Ord i => TraversableWithIndex (i, i) (EdgeFocused i v) where
  itraverse = itraverseOf (from edgeFocused . edgeMap . itraverse . mapT)
    where
      mapT :: Applicative f => Indexed (i, i) e (f e') -> i -> Map i e -> f (Map i e')
      mapT i i1 = M.traverseWithKey (\i2 -> runIndexed i (i1, i2))
