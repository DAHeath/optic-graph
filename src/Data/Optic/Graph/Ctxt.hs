{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Data.Optic.Graph.Ctxt
  ( Ctxt(..), before, here, after
  , match, addCtxt
  , toDecomp, fromDecomp, decomp
  ) where

import           Control.Lens

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M

import           Data.Optic.Graph.Graph

data Ctxt i e v = Ctxt
  { _before :: [(i, e)]
  , _here :: v
  , _after :: [(i, e)]
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Ctxt

-- | Decompose the graph into the context about the given index/vertex and
-- the remainder of the graph not in the context.
match :: Ord i => i -> v -> Graph i e v -> (Ctxt i e v, Graph i e v)
match i v g = (Ctxt (filter ((/= i) . fst) $ g ^@.. iedgesTo i)
                    v (g ^@.. iedgesFrom i), delIdx i g)

-- | Add the vertex and edges described by the context to the graph. Note that
-- if the context describes edges to/from indices which are not in the graph already
-- then those edges will not be added.
addCtxt :: Ord i => i -> Ctxt i e v -> Graph i e v -> Graph i e v
addCtxt i (Ctxt bef v aft) g =
  foldr (uncurry (i `addEdge`))
    (foldr (uncurry (`addEdge` i)) (addVert i v g) bef)
    aft

-- | A full decomposition of the graph into contexts.
toDecomp :: Ord i => Graph i e v -> Map i (Ctxt i e v)
toDecomp g = fst $ foldr (\(i, v) (cs, g') ->
                                  let (c, g'') = match i v g'
                                  in (M.insert i c cs, g''))
                         (M.empty, g)
                         (g ^@.. iallVerts)

-- | Construct a graph from a decomposition.
fromDecomp :: Ord i => Map i (Ctxt i e v) -> Graph i e v
fromDecomp = foldl (flip (uncurry addCtxt)) empty . M.toList

-- | The isomorphism between graphs and their decompositions.
decomp :: (Ord i, Ord i')
       => Iso (Graph i e v) (Graph i' e' v') (Map i (Ctxt i e v)) (Map i' (Ctxt i' e' v'))
decomp = iso toDecomp fromDecomp

instance Functor (Ctxt i e) where
  fmap f = here %~ f
