{-# LANGUAGE RankNTypes #-}
module Data.Optic.Internal.GraphTest where

import Control.Lens
import Control.Monad.State

import Data.Optic.Directed.Internal
import qualified Data.Set as S

import Prelude hiding (reverse)

import Test.Hspec
import Test.QuickCheck

type Bitraversal s t a b c d =
  forall f. Applicative f => (a -> f b) -> (c -> f d) -> s -> f t

type IGraph f = Graph f Int Int Int

prop_reverseInvolutive :: IGraph -> Bool
prop_reverseInvolutive g = reverse (reverse g) == g

prop_bitravPure :: Bitraversal IGraph IGraph Int Int Int Int -> IGraph -> Bool
prop_bitravPure t g = t pure pure g == (pure g :: Identity IGraph)

prop_top :: IGraph -> Bool
prop_top g = case top pure pure g of
    Nothing -> True
    Just tr -> g == runIdentity tr

prop_topMeansDag :: IGraph -> Bool
prop_topMeansDag g = case top pure pure g of
  Nothing -> True
  Just tr ->
    let g' = runIdentity tr
    in all (\i -> i `notElem` descendants i g') (idxs g')

prop_travPure :: Traversal IGraph IGraph Int Int -> IGraph -> Bool
prop_travPure t g = t pure g == (pure g :: Identity IGraph)

prop_addVertOrder :: Int -> Int -> IGraph -> Bool
prop_addVertOrder k v g = ((order g :: Integer) < order (addVert k v g)) || k `elem` idxs g

prop_addVertGet :: Int -> Int -> IGraph -> Bool
prop_addVertGet k v g = addVert k v g ^. at k == Just v

prop_addEdgeSize :: Int -> Int -> Int -> IGraph -> Bool
prop_addEdgeSize k1 k2 e g =
  ((size g :: Integer) < size (addEdge (Pair k1 k2) e g))
  || k1 `notElem` idxs g
  || k2 `notElem` idxs g
  || elemEdge (Pair k1 k2) g

-- prop_decomp :: IGraph -> Bool
-- prop_decomp g = case matchAny g of
--   Nothing -> null g
--   Just d -> fromDecomp d == g

prop_addDelEdge :: Int -> Int -> Int -> IGraph -> Bool
prop_addDelEdge k1 k2 e g =
  let k = Pair k1 k2
  in delEdge k (addEdge k e g) == g || elemEdge k g

prop_addDelVert :: Int -> Int -> IGraph -> Bool
prop_addDelVert k v g =
  delIdx k (addVert k v g) == g || elemVert k g

prop_filterVertsEdges :: Int -> Int -> Int -> Int -> Int -> IGraph -> Bool
prop_filterVertsEdges i1 i2 v v' e g =
  let added = addEdge (Pair i1 i2) e $ addVert i1 v $ addVert i2 v' g
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
