{-# LANGUAGE DeriveDataTypeable
           , DeriveFoldable
           , FlexibleContexts
           , FlexibleInstances
           , MultiParamTypeClasses
           , NoMonomorphismRestriction
           , RankNTypes
           , TemplateHaskell
           , TypeFamilies
           , UndecidableInstances
           , ViewPatterns
           #-}
module Data.Optic.Internal.Graph
  ( OrdFunctor(..), ArbFrom(..), Directed(..)
  , Graph(..), vertMap, edgeMap
  , allVerts, iallVerts
  , edge
  , edgesTo, edgesFrom, iedgesTo, iedgesFrom
  , allEdges, iallEdges
  , idxs, idxSet
  , empty
  , fromLists, fromListsWith
  , union, unionWith
  , addVert, addVertWith
  , addEdge, addEdgeWith
  , delVert
  , delEdgeBy, delEdge
  , delIdx
  , filterVerts, ifilterVerts
  , filterEdges, ifilterEdges
  , filterIdxs
  , reverse
  , cartesianProduct, cartesianProductWith

  , successors, predecessors
  , descendants, ancestors
  , connections
  , order, size
  , elemVert, elemEdge
  , backEdges
  , withoutBackEdges

  , ibitraverse
  , reached, reaches, between

  , mapVert, imapVert
  , mapEdge, imapEdge

  , foldVert, ifoldVert
  , foldEdge, ifoldEdge
  , foldIdx

  , travVert, itravVert
  , travEdge, itravEdge

  , idfs
  , idfsVert, idfsEdge
  , idfs_, idfsVert_, idfsEdge_
  , dfs, dfsVert, dfsEdge
  , dfs_, dfsVert_, dfsEdge_, dfsIdx_
  , dfsIdxs

  , ibfs
  , ibfsVert, ibfsEdge
  , ibfs_, ibfsVert_, ibfsEdge_
  , bfs, bfsVert, bfsEdge
  , bfs_, bfsVert_, bfsEdge_, bfsIdx_
  , bfsIdxs

  , itop
  , itopVert, itopEdge
  , itop_, itopVert_, itopEdge_
  , top, topVert, topEdge
  , top_, topVert_, topEdge_, topIdx_
  , topIdxs

  , idfsFrom
  , idfsFromVert, idfsFromEdge
  , idfsFrom_, idfsFromVert_, idfsFromEdge_
  , dfsFrom, dfsFromVert, dfsFromEdge
  , dfsFrom_, dfsFromVert_, dfsFromEdge_, dfsFromIdx_
  , dfsFromIdxs

  , ibfsFrom
  , ibfsFromVert, ibfsFromEdge
  , ibfsFrom_, ibfsFromVert_, ibfsFromEdge_
  , bfsFrom, bfsFromVert, bfsFromEdge
  , bfsFrom_, bfsFromVert_, bfsFromEdge_, bfsFromIdx_
  , bfsFromIdxs

  , ipath
  , ipathVert, ipathEdge
  , ipath_, ipathVert_, ipathEdge_
  , path, pathVert, pathEdge
  , path_, pathVert_, pathEdge_, pathIdx_
  , pathIdxs
  ) where

import           Control.Arrow (first)
import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Loops (whileM, whileM_)

import           Data.Data (Data)
import           Data.Ord (comparing)
import           Data.Maybe (fromMaybe, maybeToList, mapMaybe)
import           Data.List (partition, minimumBy)
import           Data.Foldable
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Sequence as Seq

import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Semigroup

import           Prelude hiding (reverse)

import           Test.QuickCheck.Arbitrary
import qualified Test.QuickCheck.Gen as G

data Graph f i e v = Graph
  { _vertMap :: Map i v
  , _edgeMap :: Map (f i) e
  } deriving (Show, Read, Eq, Ord, Data)
makeLenses ''Graph

data Action f i e v
  = Vert i v
  | Edge (f i) e
  deriving (Show, Read, Eq, Ord, Data)
makePrisms ''Action

class Directed f where
  start :: Ord a => f a -> Set a
  end :: Ord a => f a -> Set a

iedgesTo :: (Directed f, Ord i) => i -> IndexedTraversal' (f i) (Graph f i e v) e
iedgesTo e = edgeMap . itraversed . indices (\i -> e `elem` end i)

edgesTo :: (Directed f, Ord i) => i -> Traversal' (Graph f i e v) e
edgesTo = iedgesTo

iedgesFrom :: (Directed f, Ord i) => i -> IndexedTraversal' (f i) (Graph f i e v) e
iedgesFrom s = edgeMap . itraversed . indices (\i -> s `elem` start i)

edgesFrom :: (Directed f, Ord i) => i -> Traversal' (Graph f i e v) e
edgesFrom = iedgesFrom

successors :: (Directed f, Ord i) => Graph f i e v -> i -> Set i
successors g s = S.unions $ map (end . fst) $ g ^@.. iedgesFrom s

predecessors :: (Directed f, Ord i) => Graph f i e v -> i -> Set i
predecessors g e = S.unions $ map (start . fst) $ g ^@.. iedgesTo e

reverse :: (Foldable f, Reversing (f i), Ord i, Ord (f i)) => Graph f i e v -> Graph f i e v
reverse g = foldr (\(i, e) -> addEdge (reversing i) e) onlyVerts (g ^@.. iallEdges)
  where
    onlyVerts = Graph (g ^. vertMap) M.empty

order :: Integral n => Graph f i e v -> n
order = toEnum . lengthOf allVerts

size :: Integral n => Graph f i e v -> n
size = toEnum . lengthOf allEdges

elemVert :: Ord i => i -> Graph f i e v -> Bool
elemVert i g = not $ null (g ^? vertMap . ix i)

elemEdge :: (Ord i, Ord (f i)) => f i -> Graph f i e v -> Bool
elemEdge i g = not $ null (g ^? edgeMap . ix i)

allVerts :: Traversal (Graph f i e v) (Graph f i e v') v v'
allVerts = iallVerts

iallVerts :: IndexedTraversal i (Graph f i e v) (Graph f i e v') v v'
iallVerts = vertMap . itraverse . indexed

edge :: Ord (f i) => f i -> Traversal' (Graph f i e v) e
edge i = edgeMap . ix i

allEdges :: Traversal (Graph f i e v) (Graph f i e' v) e e'
allEdges = iallEdges

iallEdges :: IndexedTraversal (f i) (Graph f i e v) (Graph f i e' v) e e'
iallEdges = edgeMap . itraverse . indexed

idxs :: Graph f i e v -> [i]
idxs = views vertMap M.keys

idxSet :: Graph f i e v -> Set i
idxSet = views vertMap M.keysSet

empty :: Graph f i e v
empty = Graph M.empty M.empty

fromListsWith :: (Foldable f, Ord i, Ord (f i))
              => (e -> e -> e) -> (v -> v -> v)
              -> [(i, v)] -> [(f i, e)] -> Graph f i e v
fromListsWith fe fv vs =
  foldr (uncurry (addEdgeWith fe)) (foldr (uncurry (addVertWith fv)) empty vs)

fromLists :: (Foldable f, Ord i, Ord (f i)) => [(i, v)] -> [(f i, e)] -> Graph f i e v
fromLists = fromListsWith const const

addVertWith :: Ord i => (v -> v -> v) -> i -> v -> Graph f i e v -> Graph f i e v
addVertWith fv i v = vertMap %~ M.insertWith fv i v

addVert :: Ord i => i -> v -> Graph f i e v -> Graph f i e v
addVert = addVertWith const

addEdgeWith :: (Foldable f, Ord i, Ord (f i))
            => (e -> e -> e) -> f i -> e -> Graph f i e v -> Graph f i e v
addEdgeWith fe i e g = g &
    if all (\i' -> has (ix i') g) i
    then edgeMap %~ M.insertWith fe i e
    else id

addEdge :: (Foldable f, Ord i, Ord (f i))
        => f i -> e -> Graph f i e v -> Graph f i e v
addEdge = addEdgeWith const

unionWith :: (Ord i, Ord (f i)) => (e -> e -> e) -> (v -> v -> v)
          -> Graph f i e v -> Graph f i e v -> Graph f i e v
unionWith fe fv (Graph v1 f1) (Graph v2 f2) =
    Graph (M.unionWith fv v1 v2)
          (M.unionWith fe f1 f2)

union :: (Ord i, Ord (f i)) => Graph f i e v -> Graph f i e v -> Graph f i e v
union = unionWith const const

delIdx :: (Foldable f, Ord i) => i -> Graph f i e v -> Graph f i e v
delIdx i g = g & vertMap %~ M.delete i
               & edgeMap %~ M.filterWithKey (\i' _ -> i `notElem` i')

delEdge :: Ord (f i) => f i -> Graph f i e v -> Graph f i e v
delEdge = delEdgeBy (const True)

delEdgeBy :: Ord (f i) => (e -> Bool) -> f i -> Graph f i e v -> Graph f i e v
delEdgeBy p i = edgeMap . at i %~ mfilter (not . p)

delVert :: (Foldable f, Eq v, Ord i) => v -> Graph f i e v -> Graph f i e v
delVert v = filterVerts (not . (==) v)

ifilterVerts :: (Foldable f, Ord i) => (i -> v -> Bool) -> Graph f i e v -> Graph f i e v
ifilterVerts p g =
  let meetsP = g & vertMap %~ M.filterWithKey p
  in foldr delIdx meetsP (idxSet g `S.difference` idxSet meetsP)

filterVerts :: (Foldable f, Ord i) => (v -> Bool) -> Graph f i e v -> Graph f i e v
filterVerts p = ifilterVerts (const p)

ifilterEdges :: Ord (f i) => (f i -> e -> Bool) -> Graph f i e v -> Graph f i e v
ifilterEdges p g =
    foldr (\(i, _) -> delEdgeBy (not . p i) i) g (g ^@.. iallEdges)

filterEdges :: Ord (f i) => (e -> Bool) -> Graph f i e v -> Graph f i e v
filterEdges p = ifilterEdges (const p)

filterIdxs :: (Foldable f, Ord i) => (i -> Bool) -> Graph f i e v -> Graph f i e v
filterIdxs p g = foldr delIdx g (filter (not . p) (idxs g))

class OrdFunctor f where
  omap :: Ord b => (a -> b) -> f a -> f b

instance OrdFunctor Set where
  omap = S.map

cartesianProduct :: (OrdFunctor f, Foldable f, Ord (f i3), Ord i3)
                 => (i1 -> i2 -> i3)
                 -> (v1 -> v2 -> v3)
                 -> Graph f i1 e v1 -> Graph f i2 e v2 -> Graph f i3 e v3
cartesianProduct = cartesianProductWith const const

cartesianProductWith :: (OrdFunctor f, Foldable f, Ord (f i3), Ord i3)
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
       (i1, e) <- es1
       return (omap (`fi` i2) i1, e)
     es2' = do
       (i1, _) <- vs1
       (i2, e) <- es2
       return (omap (i1 `fi`) i2, e)
     in fromListsWith fe fv vs (es1' ++ es2')

-- | If the highest index of the start of the edge occur after the lowest index
-- of the end of the edge, then the edge is a backedge.
backEdges :: (Directed f, Ord i) => Graph f i e v -> [(f i, e)]
backEdges g = filter (\(i, _) -> fromMaybe False (do
  bef <- fst <$> S.maxView (start i)
  aft <- fst <$> S.minView (end i)
  return (bef >= aft))) (g ^@.. iallEdges)

withoutBackEdges :: (Ord i, Ord (f i), Directed f) => Graph f i e v -> Graph f i e v
withoutBackEdges g = ifilterEdges (\i _ -> i `notElem` map fst (backEdges g)) g

connections :: (OrdFunctor f, Ord i, Ord v) => Graph f i e v -> [(f (i, v), e)]
connections g = map (first (omap (\i -> (i, g ^?! ix i)))) (g ^@.. iallEdges)

descendants :: (Ord i, Ord (f i), Foldable f, Directed f)
            => i -> Graph f i e v -> Set i
descendants i g = S.unions $ map (end.fst) $ reached i g ^@.. iallEdges

ancestors :: (Ord i, Ord (f i), Foldable f, Directed f)
          => i -> Graph f i e v -> Set i
ancestors i g = S.unions $ map (start.fst) $ reaches i g ^@.. iallEdges

instance (Ord i, Ord (f i)) => Monoid (Graph f i e v) where
  mempty = empty
  mappend = union

instance (Ord i, Ord (f i)) => Semigroup (Graph f i e v)
instance AsEmpty (Graph f i e v) where
  _Empty = nearly empty (\g -> null (g ^. vertMap) && null (g ^. edgeMap))

type instance Index (Graph f i e v) = i
type instance IxValue (Graph f i e v) = v
instance Ord i => Ixed (Graph f i e v)
instance Ord i => At (Graph f i e v) where
  at i = vertMap . at i

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
  bimap fe fv (Graph vs es) = Graph (M.map fv vs) (M.map fe es)

instance Bifoldable (Graph f i) where
  bifoldr fe fv acc g = execState (bitraverse_ (modify . fe) (modify . fv) g) acc

instance Ord i => Bitraversable (Graph f i) where
  bitraverse fe fv (Graph vs es) =
    Graph <$> traverse fv vs <*> traverse fe es

instance (Foldable f, Reversing (f i), Ord i, Ord (f i)) => Reversing (Graph f i e v) where
  reversing = reverse

newtype EdgeFocused f i v e = EdgeFocused { getEdgeFocused :: Graph f i e v }
  deriving (Show, Read, Eq, Ord, Data)

edgeFocused :: Iso (Graph f i e v) (Graph f i' e' v')
                   (EdgeFocused f i v e) (EdgeFocused f i' v' e')
edgeFocused = iso EdgeFocused getEdgeFocused

instance Ord i => Functor (EdgeFocused f i v) where
  fmap = over (from edgeFocused . edgeMap) . fmap

instance Foldable (EdgeFocused f i v) where
  foldr = foldrOf (from edgeFocused . allEdges)

instance Ord i => Traversable (EdgeFocused f i v) where
  traverse = traverseOf (from edgeFocused . allEdges)

instance (Ord i, i ~ i', v ~ v')
  => Each (EdgeFocused f i v e) (EdgeFocused f i' v' e') e e' where
  each = traversed

instance Ord i => FunctorWithIndex (f i) (EdgeFocused f i v)
instance Ord i => FoldableWithIndex (f i) (EdgeFocused f i v)
instance Ord i => TraversableWithIndex (f i) (EdgeFocused f i v) where
  itraverse = from edgeFocused . edgeMap . itraverse

class ArbFrom f where
  arbFrom :: Ord a => [a] -> G.Gen (f a)

instance ArbFrom Set where
  arbFrom ks = S.fromList <$> G.listOf (G.elements ks)

instance (Ord i, Arbitrary i, Arbitrary e, Arbitrary v, ArbFrom f, Foldable f, Ord (f i))
  => Arbitrary (Graph f i e v) where
  arbitrary = do
    ks <- arbitrary
    vs <- arbVerts ks
    es <- if null ks then return [] else G.listOf (arbEdge ks)
    return (fromLists vs es)
    where
      arbVerts = traverse (\i -> (\v -> (i, v)) <$> arbitrary)
      arbEdge ks = do
        i <- arbFrom ks
        e <- arbitrary
        return (i, e)
      shrink = const []

idfs, ibfs, irevBfs, ibitraverse
  :: (Applicative g, Ord i, Ord (f i), Foldable f, Directed f)
  => (f i -> e -> g e')
  -> (i -> v -> g v')
  -> Graph f i e v -> g (Graph f i e' v')
idfs fe fv = travActs fe fv dfs'
ibfs fe fv = travActs fe fv bfs'
irevBfs fe fv = travActs fe fv revBfs'
ibitraverse = idfs

idfsFrom, ibfsFrom, irevBfsFrom
  :: (Foldable f, Directed f, Applicative g, Ord i, Ord (f i))
  => i
  -> (f i -> e -> g e)
  -> (i -> v -> g v)
  -> Graph f i e v -> g (Graph f i e v)
idfsFrom i fe fv g =
  let g' = travActs fe fv (dfsFrom' i) g
  in union <$> g' <*> pure g
ibfsFrom i fe fv g =
  let g' = travActs fe fv (bfsFrom' i) g
  in union <$> g' <*> pure g
irevBfsFrom i fe fv g =
  let g' = travActs fe fv (revBfsFrom' i) g
  in union <$> g' <*> pure g

itop :: (Directed f, Foldable f, Applicative g, Ord i, Ord (f i))
     => (f i -> e -> g e')
     -> (i -> v -> g v')
     -> Graph f i e v -> Maybe (g (Graph f i e' v'))
itop fe fv g = actionsToGraph fe fv <$> evalStateT top' (S.empty, g)

dfs', bfs', revBfs' :: (Foldable f, Directed f, Ord i)
                    => Graph f i e v -> State (Set i) [Action f i e v]
dfs' = promoteFrom dfsFrom'
bfs' = promoteFrom bfsFrom'
revBfs' = promoteFrom revBfsFrom'

reached, reaches :: (Directed f, Foldable f, Ord i, Ord (f i))
                 => i -> Graph f i e v -> Graph f i e v
reached i = runIdentity . travActs (\_ e -> Identity e) (\_ v -> Identity v) (bfsFrom' i)
reaches i = runIdentity . travActs (\_ e -> Identity e) (\_ v -> Identity v) (revBfsFrom' i)

between :: (Directed f, Foldable f, Ord (f i), Ord i)
        => i -> i -> Graph f i e v -> Graph f i e v
between i1 i2 g =
  let is1 = idxSet (reached i1 g)
      is2 = idxSet (reaches i2 g)
      is = S.intersection is1 is2
  in filterIdxs (`elem` is) g

ipath :: (Applicative g, Ord i, Foldable f, Ord (f i), Directed f)
      => i -> i
      -> (f i -> e -> g e)
      -> (i -> v -> g v)
      -> Graph f i e v -> Maybe (g (Graph f i e v))
ipath i1 i2 fe fv g = do
  m <- dijkstra' (const (1 :: Integer)) i1 g
  acs <- recAcs m i2
  let g' = actionsToGraph fe fv acs
  return (union <$> g' <*> pure g)
  where
    recAcs m i =
      if i == i1 then (\v -> [Vert i v]) <$> g ^. at i
      else do
        (fi, i', e, v) <- M.lookup i m
        acs <- recAcs m i'
        return (Vert i v : Edge fi e : acs)

dfsFrom', bfsFrom', revBfsFrom'
  :: (Foldable f, Directed f, Ord i)
  => i -> Graph f i e v -> State (Set i) [Action f i e v]
dfsFrom' i g = do
  b <- contains i <<.= True
  fmap fold $ forM (guard (not b) >> g ^? ix i) $ \v ->
    fmap ((Vert i v:) . concat) $ forM (g ^@.. iedgesFrom i) $ \(i', e) ->
      (Edge i' e:) <$> (concat <$> traverse (`dfsFrom'` g) (S.toList $ end i'))

bfsFrom' start g = evalStateT ((++) <$> visit start <*> loop) Seq.empty
  where
    loop =
      fmap fold $ whileM (gets $ not . null) $ do
        i <- state (\(Seq.viewl -> h Seq.:< t) -> (h, t))
        fmap fold $ forM (g ^@.. iedgesFrom i) $ \(i', e) ->
          (Edge i' e:) <$> (concat <$> traverse visit (S.toList $ end i'))
    visit i = do
      b <- lift (use $ contains i)
      fmap maybeToList $ forM (guard (not b) >> g ^? ix i) $ \v -> do
        lift (contains i .= True)
        modify (Seq.|> i)
        return $ Vert i v

revBfsFrom' end g = evalStateT ((++) <$> visit end <*> loop) Seq.empty
  where
    loop =
      fmap fold $ whileM (gets $ not . null) $ do
        i <- state (\(Seq.viewl -> h Seq.:< t) -> (h, t))
        fmap fold $ forM (g ^@.. iedgesTo i) $ \(i', e) ->
          (Edge i' e:) <$> (concat <$> traverse visit (S.toList $ start i'))
    visit i = do
      b <- lift (use $ contains i)
      fmap maybeToList $ forM (guard (not b) >> g ^? ix i) $ \v -> do
        lift (contains i .= True)
        modify (Seq.|> i)
        return $ Vert i v

top' :: (Ord i, Ord (f i), Directed f)
     => StateT (Set i, Graph f i e v) Maybe [Action f i e v]
top' = do
  theSet <~ uses theGraph noIncoming
  acs <- fmap concat $ whileM (uses theSet $ not . null) $ do
    i <- zoom theSet $ state S.deleteFindMin
    g <- use theGraph
    v <- lift $ g ^. at i
    (Vert i v:) <$> forM (g ^@.. iedgesFrom i) (\(i', e) -> do
      g' <- theGraph <%= delEdge i'
      when (all (\i'' -> hasn't (edgesTo i'') g') (end i')) (theSet %= S.union (end i'))
      return $ Edge i' e)
  guard =<< uses theGraph (nullOf allEdges)
  return acs
  where
    hasIncoming g = S.unions $ map (end . fst) $ g ^@.. iallEdges
    noIncoming g = idxSet g `S.difference` hasIncoming g
    theSet = _1
    theGraph = _2

dijkstra', bellmanFord' :: (Ord i, Ord n, Num n, Foldable f, Directed f)
                        => (e -> n) -> i -> Graph f i e v
                        -> Maybe (Map i (f i, i, e, v))
dijkstra' weight i g = fmap (view _1) $ (`execStateT` (M.empty, M.empty, idxSet g)) $ do
  dists . at i ?= 0
  whileM_ (uses iSet $ not . null) $ do
    ds <- use dists
    near <- minimumBy (\i1 i2 -> cmp (M.lookup i1 ds) (M.lookup i2 ds)) . S.toList <$> use iSet
    iSet %= S.delete near
    forM_ (g ^@.. iedgesFrom near) $ \(i', e) -> do
      ds' <- use dists
      let alt = (+ weight e) <$> M.lookup near ds'
      forM_ (end i') (\i'' ->
        when (cmp alt (M.lookup i'' ds') == LT) $ do
          v <- lift $ g ^. at i''
          dists . at i'' .= alt
          actsTo . at i'' ?= (i', near, e, v))
  where
    actsTo = _1
    dists = _2
    iSet = _3
    cmp md1 md2 = maybe GT (\d1 -> maybe LT (compare d1) md2) md1

bellmanFord' weight i g = fmap fst $ (`execStateT` (M.empty, M.empty)) $ do
  dists . at i ?= 0
  forOf_ allVerts g $ \_ ->
    iterEdgeWeights $ \i' i1 i2 e d -> do
      v <- lift $ g ^. at i2
      dists . at i2 ?= d
      actsTo . at i2 ?= (i', i1, e, v)
  iterEdgeWeights (\_ _ _ _ _ -> mzero)
  where
    -- call the action when a lower weight path is found
    iterEdgeWeights ac =
      iforOf_ iallEdges g $ \i e -> do
        let w = weight e
        ds <- use dists
        let (i1, md1) = minimumBy (comparing snd) $
              map (\i' -> (i', i' `M.lookup` ds)) (S.toList (start i))
        forM_ (end i) $ \i2 -> do
          let md2 = M.lookup i2 ds
          forM_ (cmp md1 w md2) (ac i i1 i2 e)

    -- d1 + w < d2? Nothing represents infinite weight.
    cmp md1 w md2 = do
      d1 <- md1
      case md2 of
        Nothing -> Just (d1 + w)
        Just d2 -> if d1 + w < d2 then Just (d1 + w) else Nothing
    actsTo = _1
    dists = _2

promoteFrom :: Ord i
            => (i -> Graph f i e v -> State (Set i) [Action f i e v])
            -> Graph f i e v -> State (Set i) [Action f i e v]
promoteFrom fr g = do
  s <- gets $ S.difference $ idxSet g
  if null s
  then return []
  else (++) <$> fr (S.findMin s) g <*> promoteFrom fr g

-- | Promote a stateful generator of graph actions to a indexed bitraversal.
travActs :: (Ord i, Applicative g, Foldable f, Ord (f i))
         => (f i -> e -> g e')
         -> (i -> v -> g v')
         -> (Graph f i e v -> State (Set i) [Action f i e v])
         -> Graph f i e v -> g (Graph f i e' v')
travActs fe fv trav g = actionsToGraph fe fv $ evalState (trav g) S.empty

-- | Convert a list of actions to a graph using the given applicative functions.
actionsToGraph :: (Ord i, Applicative g, Foldable f, Ord (f i))
               => (f i -> e -> g e')
               -> (i -> v -> g v')
               -> [Action f i e v] -> g (Graph f i e' v')
actionsToGraph fe fv acs = construct <$> traverse flat acs
  where
    flat (Vert i v) = Vert i <$> fv i v
    flat (Edge i e) = Edge i <$> fe i e
    act (Vert i v) = addVert i v
    act (Edge i e) = addEdge i e
    construct acs' =
      let (vs, es) = partition (has _Vert) acs'
      in foldr act (foldr act empty vs) es

mapVert :: (v -> v') -> Graph f i e v -> Graph f i e v'
mapVert = fmap

-- | Apply the given function to all vertices, taking each vertex's index as an
-- additional argument.
imapVert :: (i -> v -> v') -> Graph f i e v -> Graph f i e v'
imapVert = imap

-- | Apply the given function to all edges.
mapEdge :: Ord i => (e -> e') -> Graph f i e v -> Graph f i e' v
mapEdge = under (from edgeFocused) . fmap

-- | Apply the given function to all edges, taking each edge's indices as
-- additional arguments.
imapEdge :: Ord i => (f i -> e -> e') -> Graph f i e v -> Graph f i e' v
imapEdge = under (from edgeFocused) . imap

-- | Aggregate the vertices.
foldVert :: (v -> b -> b) -> b -> Graph f i e v -> b
foldVert = foldr

-- | Aggregate the vertices with the vertex index as an additional argument.
ifoldVert :: (i -> v -> b -> b) -> b -> Graph f i e v -> b
ifoldVert = ifoldr

-- | Aggregate the edges.
foldEdge :: (e -> b -> b) -> b -> Graph f i e v -> b
foldEdge f acc g = foldr f acc (EdgeFocused g)

-- | Aggregate the edges with the edge indices as additional arguments.
ifoldEdge :: Ord i => (f i -> e -> b -> b) -> b -> Graph f i e v -> b
ifoldEdge f acc g = ifoldr f acc (EdgeFocused g)

-- | Aggregate the indices.
foldIdx :: (i -> b -> b) -> b -> Graph f i e v -> b
foldIdx f acc g = foldr f acc (idxs g)

-- | Traverse the vertices.
travVert :: Applicative g => (v -> g v') -> Graph f i e v -> g (Graph f i e v')
travVert = traverse

-- | Indexed vertex traversal.
itravVert :: Applicative g => (i -> v -> g v') -> Graph f i e v -> g (Graph f i e v')
itravVert = itraverse

-- | Traverse the edges.
travEdge :: Applicative g => (e -> g e') -> Graph f i e v -> g (Graph f i e' v)
travEdge = allEdges

-- | Indexed edge traversal.
itravEdge :: (Ord i, Applicative g)
          => (f i -> e -> g e') -> Graph f i e v -> g (Graph f i e' v)
itravEdge f g = getEdgeFocused <$> itraverse f (EdgeFocused g)

data Trav g f t i e e' v v' = Trav
  { getitrav :: (t i -> e -> f e')
             -> (i -> v -> f v')
             -> Graph t i e v -> g (f (Graph t i e' v'))
  , getitravVert :: (e' ~ e)
                 => (i -> v -> f v')
                 -> Graph t i e v -> g (f (Graph t i e v'))
  , getitravEdge :: (v' ~ v)
                 => (t i -> e -> f e')
                 -> Graph t i e v -> g (f (Graph t i e' v))
  , getitrav_ :: forall e'' v''. (e' ~ e, v' ~ v)
              => (t i -> e -> f e'')
              -> (i -> v -> f v'')
              -> Graph t i e v -> g (f ())
  , getitravVert_ :: forall v''. (e' ~ e, v' ~ v)
                  => (i -> v -> f v'')
                  -> Graph t i e v -> g (f ())
  , getitravEdge_ :: forall e'' v''. (e' ~ e, v' ~ v)
                  => (t i -> e -> f e'')
                  -> Graph t i e v -> g (f ())
  , gettrav :: (e -> f e')
            -> (v -> f v')
            -> Graph t i e v -> g (f (Graph t i e' v'))
  , gettravVert :: (e' ~ e)
                => (v -> f v')
                -> Graph t i e v -> g (f (Graph t i e' v'))
  , gettravEdge :: (v' ~ v)
                => (e -> f e')
                -> Graph t i e v -> g (f (Graph t i e' v'))
  , gettrav_ :: forall e'' v''. (e' ~ e, v' ~ v)
             => (e -> f e'')
             -> (v -> f v'')
             -> Graph t i e v -> g (f ())
  , gettravVert_ :: forall v''. (e' ~ e, v' ~ v)
                 => (v -> f v'')
                 -> Graph t i e v -> g (f ())
  , gettravEdge_ :: forall e''. (e' ~ e, v' ~ v)
                 => (e -> f e'')
                 -> Graph t i e v -> g (f ())
  , gettravIdx_ :: forall i'. (e' ~ e, v' ~ v)
                => (i -> f i')
                -> Graph t i e v -> g (f ())
  , gettravIdxs :: (e' ~ e, v' ~ v, f ~ State [i]) => Graph t i e v -> g [i]
  }

mkTrav :: (Functor g, Applicative f, Ord i)
       => (   (t i -> e -> f e')
           -> (i -> v -> f v')
           -> Graph t i e v -> g (f (Graph t i e' v')))
       -> Trav g f t i e e' v v'
mkTrav itrav =
  let theTrav = Trav
        { getitrav = itrav
        , getitravVert = itrav (const pure)
        , getitravEdge = \fe -> itrav fe (const pure)
        , getitrav_ = \fe fv -> fmap void . itrav (\i e -> fe i e *> pure e)
                                                  (\i v -> fv i v *> pure v)
        , getitravVert_ = getitrav_ theTrav (\_ _ -> pure ())
        , getitravEdge_ = \fe -> getitrav_ theTrav fe (\_ _ -> pure ())
        , gettrav = \fe fv -> itrav (const fe) (const fv)
        , gettravVert = gettrav theTrav pure
        , gettravEdge = \fe -> gettrav theTrav fe pure
        , gettrav_ = \fe fv -> fmap void . gettrav theTrav (\e -> fe e *> pure e)
                                                           (\v -> fv v *> pure v)
        , gettravVert_ = gettrav_ theTrav (\_ -> pure ())
        , gettravEdge_ = \fe -> gettrav_ theTrav fe (\_ -> pure ())
        , gettravIdx_ = \fi -> getitravVert_ theTrav (\i _ -> fi i)
        , gettravIdxs =
            fmap (\ac -> reversing $ execState ac []) . gettravIdx_ theTrav (\i -> modify (i:))
        }
  in theTrav

dfsTravs, bfsTravs :: (Applicative f, Ord i, Ord (t i), Foldable t, Directed t)
                   => Trav Identity f t i e e' v v'
dfsTravs = mkTrav (\fe fv -> Identity . idfs fe fv)
bfsTravs = mkTrav (\fe fv -> Identity . ibfs fe fv)

dfsFromTravs, bfsFromTravs
  :: (Applicative f, Ord i, e' ~ e, v' ~ v, Ord (t i), Foldable t, Directed t)
  => i -> Trav Identity f t i e e' v v'
dfsFromTravs i = mkTrav (\fe fv -> Identity . idfsFrom i fe fv)
bfsFromTravs i = mkTrav (\fe fv -> Identity . ibfsFrom i fe fv)

topTravs :: (Applicative f, Ord i, Ord (t i), Foldable t, Directed t)
         => Trav Maybe f t i e e' v v'
topTravs = mkTrav itop

pathTravs :: (Applicative f, Ord i, e' ~ e, v' ~ v, Ord (t i), Foldable t, Directed t)
          => i -> i -> Trav Maybe f t i e e' v v'
pathTravs i1 i2 = mkTrav (ipath i1 i2)

idfsVert fv  = runIdentity . getitravVert dfsTravs fv
idfsEdge fe  = runIdentity . getitravEdge dfsTravs fe
idfs_ fe fv  = runIdentity . getitrav_ dfsTravs fe fv
idfsVert_ fv = runIdentity . getitravVert_ dfsTravs fv
idfsEdge_ fe = runIdentity . getitravEdge_ dfsTravs fe
dfs fe fv    = runIdentity . gettrav dfsTravs fe fv
dfsVert fv   = runIdentity . gettravVert dfsTravs fv
dfsEdge fe   = runIdentity . gettravEdge dfsTravs fe
dfs_ fe fv   = runIdentity . gettrav_ dfsTravs fe fv
dfsVert_ fv  = runIdentity . gettravVert_ dfsTravs fv
dfsEdge_ fe  = runIdentity . gettravEdge_ dfsTravs fe
dfsIdx_ fi   = runIdentity . gettravIdx_ dfsTravs fi
dfsIdxs      = runIdentity . gettravIdxs dfsTravs

ibfsVert fv  = runIdentity . getitravVert bfsTravs fv
ibfsEdge fe  = runIdentity . getitravEdge bfsTravs fe
ibfs_ fe fv  = runIdentity . getitrav_ bfsTravs fe fv
ibfsVert_ fv = runIdentity . getitravVert_ bfsTravs fv
ibfsEdge_ fe = runIdentity . getitravEdge_ bfsTravs fe
bfs fe fv    = runIdentity . gettrav bfsTravs fe fv
bfsVert fv   = runIdentity . gettravVert bfsTravs fv
bfsEdge fe   = runIdentity . gettravEdge dfsTravs fe
bfs_ fe fv   = runIdentity . gettrav_ bfsTravs fe fv
bfsVert_ fv  = runIdentity . gettravVert_ bfsTravs fv
bfsEdge_ fe  = runIdentity . gettravEdge_ bfsTravs fe
bfsIdx_ fi   = runIdentity . gettravIdx_ bfsTravs fi
bfsIdxs      = runIdentity . gettravIdxs bfsTravs

idfsFromVert i fv  = runIdentity . getitravVert (dfsFromTravs i) fv
idfsFromEdge i fe  = runIdentity . getitravEdge (dfsFromTravs i) fe
idfsFrom_ i fe fv  = runIdentity . getitrav_ (dfsFromTravs i) fe fv
idfsFromVert_ i fv = runIdentity . getitravVert_ (dfsFromTravs i) fv
idfsFromEdge_ i fe = runIdentity . getitravEdge_ (dfsFromTravs i) fe
dfsFrom i fe fv    = runIdentity . gettrav (dfsFromTravs i) fe fv
dfsFromVert i fv   = runIdentity . gettravVert (dfsFromTravs i) fv
dfsFromEdge i fe   = runIdentity . gettravEdge (dfsFromTravs i) fe
dfsFrom_ i fe fv   = runIdentity . gettrav_ (dfsFromTravs i) fe fv
dfsFromVert_ i fv  = runIdentity . gettravVert_ (dfsFromTravs i) fv
dfsFromEdge_ i fe  = runIdentity . gettravEdge_ (dfsFromTravs i) fe
dfsFromIdx_ i fi   = runIdentity . gettravIdx_ (dfsFromTravs i) fi
dfsFromIdxs i      = runIdentity . gettravIdxs (dfsFromTravs i)

ibfsFromVert i fv  = runIdentity . getitravVert (bfsFromTravs i) fv
ibfsFromEdge i fe  = runIdentity . getitravEdge (bfsFromTravs i) fe
ibfsFrom_ i fe fv  = runIdentity . getitrav_ (bfsFromTravs i) fe fv
ibfsFromVert_ i fv = runIdentity . getitravVert_ (bfsFromTravs i) fv
ibfsFromEdge_ i fe = runIdentity . getitravEdge_ (bfsFromTravs i) fe
bfsFrom i fe fv    = runIdentity . gettrav (bfsFromTravs i) fe fv
bfsFromVert i fv   = runIdentity . gettravVert (bfsFromTravs i) fv
bfsFromEdge i fe   = runIdentity . gettravEdge (bfsFromTravs i) fe
bfsFrom_ i fe fv   = runIdentity . gettrav_ (bfsFromTravs i) fe fv
bfsFromVert_ i fv  = runIdentity . gettravVert_ (bfsFromTravs i) fv
bfsFromEdge_ i fe  = runIdentity . gettravEdge_ (bfsFromTravs i) fe
bfsFromIdx_ i fi   = runIdentity . gettravIdx_ (bfsFromTravs i) fi
bfsFromIdxs i      = runIdentity . gettravIdxs (bfsFromTravs i)

itopVert  = getitravVert topTravs
itopEdge  = getitravEdge topTravs
itop_     = getitrav_ topTravs
itopVert_ = getitravVert_ topTravs
itopEdge_ = getitravEdge_ topTravs
top       = gettrav topTravs
topVert   = gettravVert topTravs
topEdge   = gettravEdge dfsTravs
top_      = gettrav_ topTravs
topVert_  = gettravVert_ topTravs
topEdge_  = gettravEdge_ topTravs
topIdx_   = gettravIdx_ topTravs
topIdxs   = gettravIdxs topTravs

ipathVert  i1 i2 = getitravVert (pathTravs i1 i2)
ipathEdge  i1 i2 = getitravEdge (pathTravs i1 i2)
ipath_     i1 i2 = getitrav_ (pathTravs i1 i2)
ipathVert_ i1 i2 = getitravVert_ (pathTravs i1 i2)
ipathEdge_ i1 i2 = getitravEdge_ (pathTravs i1 i2)
path       i1 i2 = gettrav (pathTravs i1 i2)
pathVert   i1 i2 = gettravVert (pathTravs i1 i2)
pathEdge   i1 i2 = gettravEdge dfsTravs
path_      i1 i2 = gettrav_ (pathTravs i1 i2)
pathVert_  i1 i2 = gettravVert_ (pathTravs i1 i2)
pathEdge_  i1 i2 = gettravEdge_ (pathTravs i1 i2)
pathIdx_   i1 i2 = gettravIdx_ (pathTravs i1 i2)
pathIdxs   i1 i2 = gettravIdxs (pathTravs i1 i2)
