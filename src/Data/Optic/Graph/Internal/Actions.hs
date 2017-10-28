{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
module Data.Optic.Graph.Internal.Actions where

import           Control.Lens
import           Control.Monad.State

import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition)

import           Data.Optic.Graph.Graph

data Action i e v
  = Vert i v
  | Edge i i e
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Action

-- | Promote a partial traversal (which only reaches a portion of the graph) to
-- a full traversal by repeatedly invoking the partial traversal on non-visited
-- indices.
promoteFrom :: Ord i
            => (i -> Graph i e v -> State (Set i) [Action i e v])
            -> Graph i e v -> State (Set i) [Action i e v]
promoteFrom fr g = do
  s <- gets $ S.difference $ idxSet g
  if null s
    then return []
    else (++) <$> fr (S.findMin s) g <*> promoteFrom fr g

-- | Promote a stateful generator of graph actions to a indexed bitraversal.
travActs :: (Ord i, Applicative f)
         => (i -> i -> e -> f e')
         -> (i -> v -> f v')
         -> (Graph i e v -> State (Set i) [Action i e v])
         -> Graph i e v -> f (Graph i e' v')
travActs fe fv trav g = actionsToGraph fe fv $ evalState (trav g) S.empty

-- | Convert a list of actions to a graph using the given applicative functions.
actionsToGraph :: (Ord i, Applicative f)
               => (i -> i -> e -> f e')
               -> (i -> v -> f v')
               -> [Action i e v] -> f (Graph i e' v')
actionsToGraph fe fv acs = construct <$> traverse flat acs
  where
    flat (Vert i v) = Vert i <$> fv i v
    flat (Edge i i' e) = Edge i i' <$> fe i i' e
    act (Vert i v) = addVert i v
    act (Edge i i' e) = addEdge i i' e
    construct acs' =
      let (vs, es) = partition (has _Vert) acs'
      in foldr act (foldr act empty vs) es
