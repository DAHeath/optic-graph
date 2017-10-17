{-# LANGUAGE RankNTypes #-}
module Main where

import Control.Lens
import Test.Hspec
import Test.QuickCheck
import Data.Ord.Graph
import qualified Data.Map as M
import Prelude hiding (reverse)

main :: IO ()
main = hspec $
  describe "Graphs" $ do
    it "reversal should be involutive" (property prop_reverseInvolutive)
    it "dfs should be a valid traversal" (property (prop_bitravPure dfs))
    it "bfs should be a valid traversal" (property (prop_bitravPure bfs))
    it "travEdges should be a valid traversal" (property (prop_travPure travEdges))
    it "travVerts should be a valid traversal" (property (prop_travPure travVerts))
    it "addVert should increase order" (property prop_addVertOrder)
    it "addVert should change lookup" (property prop_addVertGet)
    it "addEdge should increase size" (property prop_addEdgeSize)
    it "decomposition should preserve structure" (property prop_decomp)
    it "delEdge should invert addEdge" (property prop_addDelEdge)
    it "delIdx should invert addVert" (property prop_addDelVert)

type IGraph = Graph Int Int Int

prop_reverseInvolutive :: IGraph -> Bool
prop_reverseInvolutive g = reverse (reverse g) == g

prop_bitravPure :: Bitraversal IGraph IGraph Int Int Int Int
              -> IGraph -> Bool
prop_bitravPure t g = t pure pure g == (pure g :: Identity IGraph)

prop_travPure :: Traversal IGraph IGraph Int Int -> IGraph -> Bool
prop_travPure t g = t pure g == (pure g :: Identity IGraph)

prop_addVertOrder :: Int -> Int -> IGraph -> Bool
prop_addVertOrder k v g = (order g < order (addVert k v g)) || k `elem` idxs g

prop_addVertGet :: Int -> Int -> IGraph -> Bool
prop_addVertGet k v g = addVert k v g ^. at k == Just v

prop_addEdgeSize :: Int -> Int -> Int -> IGraph -> Bool
prop_addEdgeSize k1 k2 e g =
  (size g < size (addEdge k1 k2 e g))
  || k1 `notElem` idxs g
  || k2 `notElem` idxs g
  || elemEdge k1 k2 g

prop_decomp :: IGraph -> Bool
prop_decomp g = fromDecomp (toDecomp g) == g

prop_addDelEdge :: Int -> Int -> Int -> IGraph -> Bool
prop_addDelEdge k1 k2 e g =
  delEdge k1 k2 (addEdge k1 k2 e g) == g || elemEdge k1 k2 g

prop_addDelVert :: Int -> Int -> IGraph -> Bool
prop_addDelVert k v g =
  delIdx k (addVert k v g) == g || elemVert k g
