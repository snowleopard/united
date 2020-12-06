{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Monoid.United where

import Algebra.Graph (Graph, vertex)
import Data.Functor
import Data.List (intercalate, sort)
import Data.Map (Map)
import Data.Set (Set)
import Data.String

import qualified Algebra.Graph as Graph
import qualified Data.Map      as Map
import qualified Data.Set      as Set

-- | A monoid with two additional properties: /commutativity/ and /idempotence/.
--
-- Laws:
-- * Commutativity: a <> b = b <> a
-- * Idempotence:   a <> a = a
class Monoid m => Semilattice m

empty :: Semilattice m => m
empty = mempty

overlay :: Semilattice m => m -> m -> m
overlay = mappend

overlays :: Semilattice m => [m] -> m
overlays = foldr overlay empty

infixr 6 <+>
(<+>) :: Semilattice m => m -> m -> m
(<+>) = overlay

-- The natural partial order on the semilattice
isContainedIn :: (Eq m, Semilattice m) => m -> m -> Bool
isContainedIn x y = x <+> y == y

-- Laws:
-- * United identity:     a <.> empty == empty <.> a == a
-- * Associativity:   a <.> (b <.> c) == (a <.> b) <.> c
-- * Distributivity:  a <.> (b <+> c) == a <.> b <+> a <.> c
--                    (a <+> b) <.> c == a <.> c <+> b <.> c
class Semilattice m => United m where
    connect :: m -> m -> m

infixr 7 <.>
(<.>) :: United m => m -> m -> m
(<.>) = connect

connects :: United m => [m] -> m
connects = foldr connect empty

-- We are using the OverloadedStrings extension for creating vertices
example :: (United m, IsString m) => m
example = overlays [ "p" <.> "q" <.> "r" <.> "s"
                   , ("r" <+> "s") <.> "t"
                   , "u"
                   , "v" <.> "x"
                   , "w" <.> ("x" <+> "y" <+> "z")
                   , "x" <.> "y" <.> "z" ]

-- Filled-in triangle
rstFace :: (United m, IsString m) => m
rstFace = "r" <.> "s" <.> "t"

-- Hollow triangle
rstSkeleton :: (United m, IsString m) => m
rstSkeleton = "r" <.> "s" <+> "r" <.> "t" <+> "s" <.> "t"

newtype Point = Point { getPoint :: String }
    deriving (Eq, Ord, IsString)

instance Show Point where
    show = getPoint

-------------------------------- Execution time --------------------------------
newtype Time = Time { getTime :: Int } deriving (Eq, Num, Ord, Show)

instance Semigroup Time where
    Time x <> Time y = Time (max x y)

instance Monoid Time where
    mempty = Time 0

instance Semilattice Time

instance United Time where
    connect (Time x) (Time y) = Time (x + y)

------------------------------- Algebraic graphs -------------------------------
-- TODO: Remove orphan instance
instance Semigroup (Graph a) where
    (<>) = Graph.overlay

instance Monoid (Graph a) where
    mempty = Graph.empty

instance Semilattice (Graph a)

instance United (Graph a) where
    connect = Graph.connect

-- TODO: Remove orphan instance
instance IsString (Graph Point) where
    fromString = vertex . Point

--------------------------------- Suffix trees ---------------------------------
newtype SuffixTree a = SuffixTree { getSuffixTree :: Map a (SuffixTree a) }
    deriving (Eq, Ord)

instance Ord a => Semigroup (SuffixTree a) where
    SuffixTree l <> SuffixTree r = SuffixTree $ Map.unionWith (<>) l r

instance Ord a => Monoid (SuffixTree a) where
    mempty = SuffixTree mempty

instance Ord a => Semilattice (SuffixTree a)

instance Ord a => United (SuffixTree a) where
    SuffixTree l `connect` r = SuffixTree (l <&> (`connect` r)) <> r

instance (Ord a, IsString a) => IsString (SuffixTree a) where
    fromString = SuffixTree . (`Map.singleton` mempty) . fromString

instance Show a => Show (SuffixTree a) where
    show st = if length parts > 1
        then "(" ++ intercalate " + " parts ++ ")"
        else concat parts
      where
        parts =
            map (\(a, n) -> show a ++
                if Map.null (getSuffixTree n) then "" else "." ++ show n) .
            Map.toList . getSuffixTree $ st

fasterIsContainedIn :: Ord a => SuffixTree a -> SuffixTree a -> Bool
fasterIsContainedIn (SuffixTree l) (SuffixTree r) =
    Map.isSubmapOfBy fasterIsContainedIn l r

toListOfWords :: SuffixTree a -> [[a]]
toListOfWords (SuffixTree m) =
    (Map.toList m >>= \(a, n) -> map (a:) (toListOfWords n))
    ++ return []

----------------------------- Simplicial complexes -----------------------------
-- A simplex is formed on a set of points
newtype Simplex a = Simplex { getSimplex :: Set a }
    deriving (Eq, Semigroup)

-- Size-lexicographic order: https://en.wikipedia.org/wiki/Shortlex_order
instance Ord a => Ord (Simplex a) where
    compare (Simplex x) (Simplex y) =
        compare (Set.size x) (Set.size y) <>
        compare x y

instance Show a => Show (Simplex a) where
    show = intercalate "." . map show . Set.toList . getSimplex

instance IsString a => IsString (Simplex a) where
    fromString = Simplex . Set.singleton . fromString

isFaceOf :: Ord a => Simplex a -> Simplex a -> Bool
isFaceOf (Simplex x) (Simplex y) = Set.isSubsetOf x y

-- A simplicial complex is a set of simplices
-- We only store maximal simplices for efficiency
newtype Complex a = Complex { getComplex :: Set (Simplex a) }
    deriving (Eq, Ord)

instance Show a => Show (Complex a) where
    show = intercalate " + " . map show . Set.toList . getComplex

instance IsString a => IsString (Complex a) where
    fromString = Complex . Set.singleton . fromString

-- Do not add a simplex if it is contained in existing ones
addSimplex :: Ord a => Simplex a -> Complex a -> Complex a
addSimplex x (Complex y)
    | any (isFaceOf x) y = Complex y
    | otherwise          = Complex (Set.insert x y)

-- Drop all non-minimal simplices
normalise :: Ord a => Complex a -> Complex a
normalise = foldr addSimplex empty . sort . Set.toList . getComplex

instance Ord a => Semigroup (Complex a) where
    Complex x <> Complex y = normalise (Complex $ x <> y)

instance Ord a => Monoid (Complex a) where
    mempty = Complex Set.empty

instance Ord a => Semilattice (Complex a)

instance Ord a => United (Complex a) where
    connect (Complex x) (Complex y) = normalise . Complex $ Set.fromList
        [ a <> b | a <- Set.toList x, b <- Set.toList y ]
