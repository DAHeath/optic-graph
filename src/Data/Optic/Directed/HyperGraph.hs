{-# LANGUAGE DeriveDataTypeable, DeriveFoldable #-}
module Data.Optic.Directed.HyperGraph
  ( HEdge(..)
  , Graph
  , module Data.Optic.Internal.Graph
  , delIdxSaveEdges
  ) where

import           Control.Lens

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Optic.Internal.Graph as I
import           Data.Optic.Internal.Graph hiding (Graph)

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

data HEdge a = HEdge (Set a) a
  deriving (Show, Read, Eq, Ord, Data, Foldable)

instance Directed HEdge where
  start (HEdge a _) = a
  end (HEdge _ a) = S.singleton a

instance OrdFunctor HEdge where
  omap f (HEdge as b) = HEdge (omap f as) (f b)

instance ArbFrom HEdge where
  arbFrom ks = do
    i1 <- arbFrom ks
    i2 <- G.elements ks
    return (HEdge i1 i2)

instance (Arbitrary a, Ord a) => Arbitrary (HEdge a) where
  arbitrary = HEdge <$> arbitrary <*> arbitrary

type Graph i e v = I.Graph HEdge i e v

-- | Delete the index from the graph. However, preserve any edges from that
-- index which satisfy the predicate (after the index is removed from the hyperedge start).
delIdxSaveEdges :: Ord i => (HEdge i -> e -> Bool) -> i -> Graph i e v -> Graph i e v
delIdxSaveEdges p i g =
  foldr (\(HEdge i1 i2, e) g' ->
        let newI = HEdge (S.filter (/= i) i1) i2 in
        g' & delEdge (HEdge i1 i2)
           & if i `notElem` i1 || p newI e
             then addEdge (HEdge (S.filter (/= i) i1) i2) e
             else id) g (g ^@.. iallEdges)
    & delIdx i
