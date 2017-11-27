{-# LANGUAGE DeriveDataTypeable, DeriveFoldable #-}
module Data.Optic.Undirected.Graph
  ( UPair
  , mkUPair
  , Graph
  , module Data.Optic.Internal.Graph
  ) where

import           Control.Lens

import           Data.Data (Data)
import qualified Data.Set as S
import qualified Data.Optic.Internal.Graph as I
import           Data.Optic.Internal.Graph hiding (Graph)

import qualified Test.QuickCheck.Gen as G

mkUPair :: Ord a => a -> a -> UPair a
mkUPair a b = if a <= b then UPair a b else UPair b a

data UPair a = UPair a a
  deriving (Show, Read, Eq, Ord, Data, Foldable)

instance OrdFunctor UPair where
  omap f (UPair a b) = mkUPair (f a) (f b)

instance ArbFrom UPair where
  arbFrom ks = do
    i1 <- G.elements ks
    i2 <- G.elements ks
    return (mkUPair i1 i2)

type Graph i e v = I.Graph UPair i e v
