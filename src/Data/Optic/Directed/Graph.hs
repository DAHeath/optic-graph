{-# LANGUAGE DeriveDataTypeable, DeriveFoldable #-}
module Data.Optic.Directed.Graph
  ( Pair(..)
  , Graph
  , module Data.Optic.Internal.Graph
  ) where

import           Control.Lens

import           Data.Data (Data)
import qualified Data.Set as S
import qualified Data.Optic.Internal.Graph as I
import           Data.Optic.Internal.Graph hiding (Graph)

import qualified Test.QuickCheck.Gen as G

data Pair a = Pair a a
  deriving (Show, Read, Eq, Ord, Data, Foldable)

instance Reversing (Pair a) where
  reversing (Pair x y) = Pair y x

instance Directed Pair where
  start (Pair a _) = S.singleton a
  end (Pair _ a) = S.singleton a

instance OrdFunctor Pair where
  omap f (Pair a b) = Pair (f a) (f b)

instance ArbFrom Pair where
  arbFrom ks = do
    i1 <- G.elements ks
    i2 <- G.elements ks
    return (Pair i1 i2)

type Graph i e v = I.Graph Pair i e v
