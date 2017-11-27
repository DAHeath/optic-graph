{-# LANGUAGE RankNTypes, FlexibleContexts, NoMonomorphismRestriction #-}
module Main where

import Control.Lens
import Control.Monad.State

import Data.Optic.Directed.HyperGraph
import qualified Data.Set as S

import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $
  describe "Graphs" $ do
    it "dfs should visit each element once" (property prop_dfsOnce)
    it "bfs should visit each element once" (property prop_bfsOnce)
    it "dfs should be a valid traversal" (property (prop_bitravPure dfs))
    it "bfs should be a valid traversal" (property (prop_bitravPure bfs))
    it "top should be a valid traversal" (property prop_top)
    it "top should succeed when no cycles" (property prop_topMeansDag)
    it "travEdge should be a valid traversal" (property (prop_travPure travEdge))
    it "travVert should be a valid traversal" (property (prop_travPure travVert))
    it "addVert should increase order" (property prop_addVertOrder)
    it "addVert should change lookup" (property prop_addVertGet)
    it "delEdge should invert addEdge" (property prop_addDelEdge)
    it "delIdx should invert addVert" (property prop_addDelVert)
    it "filterVerts should remove edges" (property prop_filterVertsEdges)
    it "elements in path should be related to source/sink" (property prop_pathRelates)
    it "if there are no back edges, ancestors exclude descendants" (property prop_ancesDesc)

type Bitraversal s t a b c d =
  forall f. Applicative f => (a -> f b) -> (c -> f d) -> s -> f t

type IGraph = Graph Int Int Int

prop_dfsOnce :: IGraph -> Bool
prop_dfsOnce g =
  let (eIs, vIs) = execState (idfs_ (\i _ -> _1 %= (i:)) (\i _ -> _2 %= (i:)) g) ([], [])
      es = g ^.. allEdges
      vs = g ^.. allVerts
  in length eIs == length es && length vIs == length vs

prop_bfsOnce :: IGraph -> Bool
prop_bfsOnce g =
  let (eIs, vIs) = execState (ibfs_ (\i _ -> _1 %= (i:)) (\i _ -> _2 %= (i:)) g) ([], [])
      es = g ^.. allEdges
      vs = g ^.. allVerts
  in length eIs == length es && length vIs == length vs

prop_bitravPure :: Bitraversal IGraph IGraph Int Int Int Int -> IGraph -> Bool
prop_bitravPure t g = t pure pure g == (pure g :: Identity IGraph)

prop_top :: IGraph -> Bool
prop_top g = case top pure pure g of
    Nothing -> True
    Just tr -> g == runIdentity tr

prop_topMeansDag :: IGraph -> Bool
prop_topMeansDag g =
  case top pure pure (withoutBackEdges g) of
    Nothing -> False
    Just tr ->
      let g' = runIdentity tr
      in g' == withoutBackEdges g

prop_travPure :: Traversal IGraph IGraph Int Int -> IGraph -> Bool
prop_travPure t g = t pure g == (pure g :: Identity IGraph)

prop_addVertOrder :: Int -> Int -> IGraph -> Bool
prop_addVertOrder k v g = ((order g :: Integer) < order (addVert k v g)) || k `elem` idxs g

prop_addVertGet :: Int -> Int -> IGraph -> Bool
prop_addVertGet k v g = addVert k v g ^. at k == Just v

prop_addEdgeSize :: HEdge Int -> Int -> IGraph -> Bool
prop_addEdgeSize k e g =
  ((size g :: Integer) < size (addEdge k e g))
  || any (`notElem` idxs g) k
  || elemEdge k g

-- prop_decomp :: IGraph -> Bool
-- prop_decomp g = case matchAny g of
--   Nothing -> null g
--   Just d -> fromDecomp d == g

prop_addDelEdge :: HEdge Int -> Int -> IGraph -> Bool
prop_addDelEdge k e g = delEdge k (addEdge k e g) == g || elemEdge k g

prop_addDelVert :: Int -> Int -> IGraph -> Bool
prop_addDelVert k v g =
  delIdx k (addVert k v g) == g || elemVert k g

prop_filterVertsEdges :: Int -> Int -> Int -> Int -> Int -> IGraph -> Bool
prop_filterVertsEdges i1 i2 v v' e g =
  let added = addEdge (HEdge (S.singleton i1) i2) e $ addVert i1 v $ addVert i2 v' g
  in (size added :: Integer) > size (filterVerts (/= v) added)

prop_pathRelates :: Int -> Int -> IGraph -> Bool
prop_pathRelates i1 i2 g =
  case pathIdx_ i1 i2 (\i -> modify (i:)) g of
    Nothing -> True
    Just tr ->
      let p = execState tr []
          in all (\i -> (i `elem` descendants i1 g) || i == i1) p
          && all (\i -> (i `elem` ancestors i2 g) || i == i2) p

prop_ancesDesc :: IGraph -> Bool
prop_ancesDesc g =
  let g' = withoutBackEdges g
      is = idxSet g'
  in all (\i ->
            let as = ancestors i g'
                ds = descendants i g'
            in as `S.intersection` ds == S.empty) is


test = fromLists [(0,3), (3,0)]
                 [ (HEdge (S.fromList []) 3, 2)
                 , (HEdge (S.fromList [0]) 3, 1)
                 -- , (HEdge (S.fromList [0, 3]) 3, 2)
                 ]

-- 6 -> 0
