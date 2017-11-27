{-# LANGUAGE TemplateHaskell
           , DeriveDataTypeable
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , RankNTypes
           , FunctionalDependencies
           , ScopedTypeVariables
           #-}

module Data.Optic.Directed.Abstract where

import           Control.Lens
import           Control.Monad.State

import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Foldable
import           Data.Semigroup
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

class (Ord t, Ord i, Ord (f i), Foldable f) => Source f i t | f i -> t where
  toTarget :: f i -> t
  fromTarget :: t -> f i

instance Ord a => Source Set a (Set a) where
  toTarget = id
  fromTarget = id

instance Ord a => Source Identity a a where
  toTarget = runIdentity
  fromTarget = Identity

class    Mappable f        where mapIt :: Ord b => (a -> b) -> f a -> f b
instance Mappable Set      where mapIt = S.map
instance Mappable Identity where mapIt = fmap

data Graph f i e v = Graph
  { _vertMap :: Map i v
  , _edgeMap' :: Map (f i) (Map i e)
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

edgeMap :: Source f i t
        => Lens (Graph f i e v) (Graph f i e' v)
                (Map t (Map i e)) (Map t (Map i e'))
edgeMap = edgeMap' . iso (M.mapKeys toTarget) (M.mapKeys fromTarget)

-- | To simplify the implementation of traversals, we record the order in which
-- the graph short be modified.
-- | A traversal which selects all vertices in the graph.
allVerts :: Traversal (Graph f i e v) (Graph f i e v') v v'
allVerts = vertMap . traverse

-- | Indexed traversal of all vertices.
iallVerts :: IndexedTraversal i (Graph f i e v) (Graph f i e v') v v'
iallVerts = vertMap . itraverse . indexed

-- | A traversal which selects the edge between two indices.
edge :: Source f i t => t -> i -> Traversal' (Graph f i e v) e
edge i1 i2 = edgeMap . ix i1 . ix i2

-- | A traversal which selects all edges in the graph.
allEdges :: Source f i t => Traversal (Graph f i e v) (Graph f i e' v) e e'
allEdges = edgeMap . traverse . traverse

-- | Indexed traversal of all edges in the graph.
iallEdges :: Source f i t
          => IndexedTraversal (t, i) (Graph f i e v) (Graph f i e' v) e e'
iallEdges =
  edgeMap .
    (\f -> itraverse
      (\i -> itraverse
        (\i' -> f (i, i')))) . indexed

-- | A traversal which selects all edges that come from a different index.
edgesTo :: Source f i t => i -> Traversal' (Graph f i e v) e
edgesTo = iedgesTo

-- | Indexed traversal of the edges that come from a different index, labelled with
-- the source index.
iedgesTo :: Source f i t => i -> IndexedTraversal' t (Graph f i e v) e
iedgesTo i = edgeMap . itraverse . indexed <. ix i

-- | Indices of the graph in ascending order.
idxs :: Graph f i e v -> [i]
idxs = views vertMap M.keys

-- | The set of all indices in the graph.
idxSet :: Graph f i e v -> Set i
idxSet = views vertMap M.keysSet

-- | A graph with no vertices and no edges.
empty :: Graph f i e v
empty = Graph M.empty M.empty

fromLists :: Source f i t
          => [(i, v)] -> [(t, i, e)] -> Graph f i e v
fromLists = fromListsWith const const

fromListsWith :: Source f i t
              => (e -> e -> e) -> (v -> v -> v)
              -> [(i, v)] -> [(t, i, e)] -> Graph f i e v
fromListsWith fe fv vs =
  foldr (\(i1, i2, e) -> addEdgeWith fe i1 i2 e) (foldr (uncurry (addVertWith fv)) empty vs)

addEdgeWith :: forall f i t e v. Source f i t
            => (e -> e -> e)
            -> t -> i -> e -> Graph f i e v -> Graph f i e v
addEdgeWith fe i1 i2 e g = g &
  if all (\i -> has (ix i) g) (fromTarget i1 :: f i) && has (ix i2) g
  then edgeMap . at i1 . non' _Empty %~ M.insertWith fe i2 e
  else id

addEdge :: Source f i t => t -> i -> e -> Graph f i e v -> Graph f i e v
addEdge = addEdgeWith const

addVert :: Ord i => i -> v -> Graph f i e v -> Graph f i e v
addVert = addVertWith const

addVertWith :: Ord i => (v -> v -> v) -> i -> v -> Graph f i e v -> Graph f i e v
addVertWith fv i v = vertMap %~ M.insertWith fv i v

union :: (Ord i, Ord (f i))
      => Graph f i e v -> Graph f i e v -> Graph f i e v
union = unionWith const const

unionWith :: (Ord i, Ord (f i))
          => (e -> e -> e) -> (v -> v -> v)
          -> Graph f i e v -> Graph f i e v -> Graph f i e v
unionWith fe fv (Graph v1 f1) (Graph v2 f2) =
  Graph (M.unionWith fv v1 v2)
        (M.unionWith (M.unionWith fe) f1 f2)

delVert :: (Eq v, Source f i t) => v -> Graph f i e v -> Graph f i e v
delVert v = filterVerts (not . (==) v)

delEdge :: Source f i t => t -> i -> Graph f i e v -> Graph f i e v
delEdge i1 i2 = edgeMap . at i1 . non' _Empty . at i2 .~ Nothing

delIdx :: Source f i t => i -> Graph f i e v -> Graph f i e v
delIdx i g = g & vertMap %~ M.delete i
               -- & edgeMap %~ M.delete i -- TODO
               & edgeMap %~ M.mapMaybe ((non' _Empty %~ M.delete i) . Just)

filterVerts :: Source f i t => (v -> Bool) -> Graph f i e v -> Graph f i e v
filterVerts p = ifilterVerts (const p)

ifilterVerts :: Source f i t => (i -> v -> Bool) -> Graph f i e v -> Graph f i e v
ifilterVerts p g =
  let meetsP = g & vertMap %~ M.filterWithKey p
  in foldr delIdx meetsP (idxSet g `S.difference` idxSet meetsP)

filterEdges :: Source f i t => (e -> Bool) -> Graph f i e v -> Graph f i e v
filterEdges p g =
  foldr (\((i1, i2), e) ->
    if p e then delEdge i1 i2 else id)
    g (g ^@.. iallEdges)

ifilterEdges :: Source f i t => (t -> i -> e -> Bool) -> Graph f i e v -> Graph f i e v
ifilterEdges p g =
  foldr (\((i1, i2), e) ->
    if p i1 i2 e then delEdge i1 i2 else id) g (g ^@.. iallEdges)

filterIdxs :: Source f i t => (i -> Bool) -> Graph f i e v -> Graph f i e v
filterIdxs p g = foldr delIdx g (filter (not . p) (idxs g))

cartesianProduct :: (Source f i1 t1, Source f i2 t2, Source f i3 t3, Mappable f)
                 => (i1 -> i2 -> i3)
                 -> (v1 -> v2 -> v3)
                 -> Graph f i1 e v1 -> Graph f i2 e v2 -> Graph f i3 e v3
cartesianProduct = cartesianProductWith const const

cartesianProductWith :: forall f t1 t2 t3 i1 i2 i3 e v1 v2 v3
                      . (Source f i1 t1, Source f i2 t2, Source f i3 t3, Mappable f)
                     => (e -> e -> e)
                     -> (v3 -> v3 -> v3)
                     -> (i1 -> i2 -> i3)
                     -> (v1 -> v2 -> v3)
                     -> Graph f i1 e v1 -> Graph f i2 e v2 -> Graph f i3 e v3
cartesianProductWith fe fv fi prod g1 g2 =
 if has _Empty g2 then empty else
 let vs1 = g1 ^@.. iallVerts
     vs2 = g2 ^@.. iallVerts
     vs = do
       (i1, v1) <- vs1
       (i2, v2) <- vs2
       return (fi i1 i2, prod v1 v2)
     es1 = g1 ^@.. iallEdges
     es2 = g2 ^@.. iallEdges
     es1' = do
       (i2, _) <- vs2
       ((is1, i1'), e) <- es1
       return ((toTarget $ mapIt (`fi` i2) (fromTarget (is1 :: t1) :: f i1)) :: t3, fi i1' i2, e)
     es2' = do
       (i1, _) <- vs1
       ((is2, i2'), e) <- es2
       return ((toTarget $ mapIt (i1 `fi`) (fromTarget (is2 :: t2) :: f i2)) :: t3, fi i1 i2', e)
     in fromListsWith fe fv vs (es1' ++ es2')

-- | The map obtained by applying f to each index of s.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
mapIdx :: (Mappable f, Ord i', Ord (f i'))
       => (i -> i') -> Graph f i e v -> Graph f i' e v
mapIdx f (Graph vs es) =
  Graph (M.mapKeys f vs)
        (M.mapKeys (mapIt f) $ fmap (M.mapKeys f) es)

-- | Traverse the indices.
-- The size of the result may be smaller if f maps two or more distinct indices to
-- the same new index. In this case the value at the greatest of the original indices
-- is retained.
travIdx :: (Mappable f, Applicative g, Ord i, Ord i', Ord (f i'))
        => (i -> g i') -> Graph f i e v -> g (Graph f i' e v)
travIdx f g =
  replace (idxs g) <$> traverse f (idxs g)
  where
    replace is is' =
      let m = M.fromList (zip is is')
      in mapIdx (\i -> m M.! i) g

type instance Index (Graph f i e v) = i
type instance IxValue (Graph f i e v) = v
instance Ord i => Ixed (Graph f i e v)
instance Ord i => At (Graph f i e v) where
  at i = vertMap . at i

instance (Ord i, Ord (f i)) => Monoid (Graph f i e v) where
  mempty = empty
  mappend = union

instance (Ord i, Ord (f i)) => Semigroup (Graph f i e v)
instance Source f i t => AsEmpty (Graph f i e v) where
  _Empty = nearly empty (\g -> null (g ^. vertMap) && null (g ^. edgeMap))

instance Functor (Graph f i e) where
  fmap = over vertMap . fmap

instance Foldable (Graph f i e) where
  foldr = foldrOf (vertMap . traverse)

instance Traversable (Graph f i e) where
  traverse = traverseOf (vertMap . traverse)

instance (i ~ i', e ~ e') => Each (Graph f i e v) (Graph f i' e' v') v v' where
  each = traversed

instance FunctorWithIndex i (Graph f i e)
instance FoldableWithIndex i (Graph f i e)
instance TraversableWithIndex i (Graph f i e) where
  itraverse = itraverseOf (vertMap . itraverse . runIndexed)

instance Bifunctor (Graph f i) where
  bimap fe fv (Graph vs es) = Graph (M.map fv vs) (M.map (M.map fe) es)

instance Bifoldable (Graph f i) where
  bifoldr fe fv acc g = execState (bitraverse_ (modify . fe) (modify . fv) g) acc

instance Ord i => Bitraversable (Graph f i) where
  bitraverse fe fv (Graph vs es) =
    Graph <$> traverse fv vs
          <*> traverse (traverse fe) es

-- instance (Ord i, Arbitrary i, Arbitrary e, Arbitrary v) => Arbitrary (Graph f i e v) where
--   arbitrary = do
--     ks <- arbitrary
--     vs <- arbVerts ks
--     es <- if null ks then return [] else G.listOf (arbEdge ks)
--     return (fromLists vs es)
--     where
--       arbVerts = traverse (\i -> (\v -> (i, v)) <$> arbitrary)
--       arbEdge ks = do
--         i1 <- G.elements ks
--         i2 <- G.elements ks
--         e <- arbitrary
--         return (i1, i2, e)
--   shrink = const []

-- | The successor indices for the given index.
-- successors :: Ord i => i -> Graph f i e v -> Set i
-- successors i = toListOf $ iedgesFrom i . asIndex

-- | The predecessor indices for the given index.
predecessors :: forall f i t e v. Source f i t => i -> Graph f i e v -> [i]
predecessors i g =
  concatMap (\i' -> toList (fromTarget i' :: f i)) $ g ^.. iedgesTo i . asIndex

-- descendants :: Ord i => i -> Graph i e v -> [i]
-- descendants i g = nub $ map (snd.fst) $ reached i g ^@.. iallEdges

-- ancestors :: Ord i => i -> Graph i e v -> [i]
-- ancestors i g = descendants i (reverse g)

-- | The number of vertices in the graph.
order :: Integral n => Graph f i e v -> n
order = toEnum . lengthOf allVerts

-- | The number of edges in the graph
size :: (Source f i t, Integral n) => Graph f i e v -> n
size = toEnum . lengthOf allEdges

-- | Is there a vertex at the index?
elemVert :: Ord i => i -> Graph f i e v -> Bool
elemVert i g = not $ null (g ^? vertMap . ix i)

-- | Is there an edge between the given indices?
elemEdge :: Source f i t => t -> i -> Graph f i e v -> Bool
elemEdge i1 i2 g = not $ null (g ^? edgeMap . ix i1 . ix i2)

-- | Find the edges in the graph which travel against the ordering of the indices.
backEdges :: forall f i t e v. Source f i t => Graph f i e v -> [((t, i), e)]
backEdges g = filter (\((is1, i2), _) -> any (i2 <=) (fromTarget is1 :: f i)) $ g ^@.. iallEdges

-- | Filter out backedges.
withoutBackEdges :: Source f i t => Graph f i e v -> Graph f i e v
withoutBackEdges g =
  ifilterEdges (\i1 i2 _ -> (i1, i2) `notElem` map fst (backEdges g)) g

-- | By default, graphs are "focused" on the vertices, meaning that common
-- typeclass instances act on the vertices. EdgeFocused provides an alternative
-- representation where the edges are the focus of the typeclasses.
newtype EdgeFocused f i v e = EdgeFocused { getEdgeFocused :: Graph f i e v }
  deriving (Show, Read, Eq, Ord, Data)

-- | Isomorphism between the graph and its edge focused equivalent.
edgeFocused :: Iso (Graph f i e v) (Graph f i' e' v')
                   (EdgeFocused f i v e) (EdgeFocused f i' v' e')
edgeFocused = iso EdgeFocused getEdgeFocused

instance Source f i t => Functor (EdgeFocused f i v) where
  fmap = over (from edgeFocused . edgeMap) . fmap . fmap

instance Source f i t => Foldable (EdgeFocused f i v) where
  foldr = foldrOf (from edgeFocused . allEdges)

instance Source f i t => Traversable (EdgeFocused f i v) where
  traverse = traverseOf (from edgeFocused . allEdges)

instance (Source f i t, i ~ i', v ~ v')
  => Each (EdgeFocused f i v e) (EdgeFocused f i' v' e') e e' where
  each = traversed

instance Source f i t => FunctorWithIndex (t, i) (EdgeFocused f i v)
instance Source f i t => FoldableWithIndex (t, i) (EdgeFocused f i v)
instance Source f i t => TraversableWithIndex (t, i) (EdgeFocused f i v) where
  itraverse = itraverseOf (from edgeFocused . edgeMap . itraverse . mapT)
    where
      mapT :: Applicative g => Indexed (t, i) e (g e') -> t -> Map i e -> g (Map i e')
      mapT i i1 = M.traverseWithKey (\i2 -> runIndexed i (i1, i2))
