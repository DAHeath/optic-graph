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

type IGraph = Graph Int Int Int

prop_reverseInvolutive :: IGraph -> Bool
prop_reverseInvolutive g = reverse (reverse g) == g

prop_bitravPure :: Bitraversal IGraph IGraph Int Int Int Int
              -> IGraph -> Bool
prop_bitravPure t g = t pure pure g == (pure g :: Identity IGraph)

prop_travPure :: Traversal IGraph IGraph Int Int -> IGraph -> Bool
prop_travPure t g = t pure g == (pure g :: Identity IGraph)

prop_addVertOrder :: Int -> Int -> IGraph -> Bool
prop_addVertOrder k v g = (order g < order (addVert k v g)) || k `elem` keys g

prop_addVertGet :: Int -> Int -> IGraph -> Bool
prop_addVertGet k v g = addVert k v g ^. at k == Just v

prop_addEdgeSize :: Int -> Int -> Int -> IGraph -> Bool
prop_addEdgeSize k1 k2 e g =
  (size g < size (addEdge k1 k2 e g))
  || k1 `notElem` keys g
  || k2 `notElem` keys g

-- | TODO this property is only true if the graph is connected.
prop_reachRebuild :: Int -> IGraph -> Bool
prop_reachRebuild k g = reached k g `union` reaches k g == g || k `notElem` keys g

prop_decomp :: IGraph -> Bool
prop_decomp g = fromDecomp (toDecomp g) == g
