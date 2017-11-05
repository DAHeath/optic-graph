{-# LANGUAGE TemplateHaskell, DeriveDataTypeable, DeriveFunctor, DeriveTraversable #-}
module Data.Optic.Graph.Ctxt
  ( Ctxt(..), before, here, after
  , Decomp(..), focus, remainder
  , match, matchAny, addCtxt
  , fromDecomp
  , decomp
  , decompose
  , neighborhood

  , degree, indegree, outdegree
  ) where

import           Control.Lens
import           Control.Comonad

import           Data.Data (Data)
import qualified Data.Set as S
import           Data.Optic.Graph.Graph

-- | A context is a view of a vertex where edges into and out of the
-- vertex can be viewed.
data Ctxt i e v = Ctxt
  { _before :: [(i, e)]
  , _here :: (i, v)
  , _after :: [(i, e)]
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)
makeLenses ''Ctxt

-- | A decomposition splits a graph into the context of some focus vertex with
-- the remainder of the graph (such that none of the context is in the reaminder).
data Decomp i e v = Decomp
  { _focus :: Ctxt i e v
  , _remainder :: Graph i e v
  } deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)
makeLenses ''Decomp

-- | Decompose the graph into the context about the given index/vertex and
-- the remainder of the graph not in the context.
match :: Ord i => i -> Graph i e v -> Maybe (Decomp i e v)
match i g = do
  v <- g ^? ix i
  return $ Decomp
    (Ctxt (g ^@.. iedgesTo i) (i, v) (g ^@.. iedgesFrom i))
    (delIdx i g)

-- | Perform a match on any index in the graph.
matchAny :: Ord i => Graph i e v -> Maybe (Decomp i e v)
matchAny g = do
  (i, _) <- S.minView (idxSet g)
  match i g

-- | Add the vertex and edges described by the context to the graph. Note that
-- if the context describes edges to/from indices which are not in the graph already
-- then those edges will not be added.
addCtxt :: Ord i => Ctxt i e v -> Graph i e v -> Graph i e v
addCtxt (Ctxt bef (i, v) aft) g =
  foldr (uncurry (i `addEdge`))
    (foldr (uncurry (`addEdge` i)) (addVert i v g) bef)
    aft

-- | Reconstruct the graph from its decomposition.
fromDecomp :: Ord i => Decomp i e v -> Graph i e v
fromDecomp (Decomp c g) = c `addCtxt` g

-- | A graph can be viewed as a decomposition.
decomp :: Ord i => Prism' (Graph i e v) (Decomp i e v)
decomp = prism' fromDecomp matchAny

-- | Fully decompose the graph into contexts.
decompose :: Ord i => Graph i e v -> [Ctxt i e v]
decompose g = case matchAny g of
  Nothing -> []
  Just (Decomp c g') -> c : decompose g'

-- | Graph decompositions form a comonad. We choose the comonad such that each
-- focus is placed in its full context.
instance Ord i => Comonad (Decomp i e) where
  extract = view (focus . here . _2)
  extend f d@(Decomp c g) =
    let c' = c & here . _2 .~ f d
        g' = foldr (\(i', _) acc ->
          case match i' (addCtxt c g) of
            Nothing -> acc
            Just dec -> addCtxt ((dec ^. focus) & here . _2 .~ f dec) acc
          ) empty (g ^@.. iallVerts)
    in Decomp c' g'

-- | Calculate a new vertex label from the context surrounding the vertex and
-- apply this function to the entire graph.
neighborhood :: Ord i => (Decomp i e v -> v') -> Graph i e v -> Graph i e v'
neighborhood f g = case matchAny g of
  Nothing -> empty
  Just dec -> fromDecomp $ extend f dec

-- | Label each vertex with the number of edges connected to it.
degree :: (Ord i, Integral n) => Graph i e v -> Graph i e n
degree = neighborhood (\(Decomp c _) ->
  toEnum $ length (c ^. before) + length (c ^. after))

-- | Label each vertex with the number of edges into it.
indegree :: (Ord i, Integral n) => Graph i e v -> Graph i e n
indegree = neighborhood (\(Decomp c _) ->
  toEnum $ length (c ^. before))

-- | Label each vertex with the number of edges out of it.
outdegree :: (Ord i, Integral n) => Graph i e v -> Graph i e n
outdegree = neighborhood (\(Decomp c _) ->
  toEnum $ length (c ^. after))
