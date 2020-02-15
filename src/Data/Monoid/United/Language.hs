{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
module Data.Monoid.United.Language where

import Data.Array
import Data.Bifunctor
import Data.Monoid

data U e a where
    Nil :: U e a
    Tip :: a -> U e a
    Bin :: e -> U e a -> U e a -> U e a
    Let :: (Ix i, Show i) => Array i (U e a) -> U e (Either i a) -> U e a

fold :: forall a b e f. Applicative f => (forall x. f x)
     -> (a -> f b)
     -> (forall x. e -> f x -> f x -> f x)
     -> (forall x i. (Ix i, Show i) => Array i (f x) -> f (Either i x) -> f x)
     -> U e a
     -> f b
fold e t b l = go t
  where
    go :: (x -> f y) -> U e x -> f y
    go t x = case x of
      Nil       -> e
      Tip a     -> t a
      Bin e x y -> b e (go t x) (go t y)
      Let arr x -> l (fmap (go t) arr) (go (either (pure . Left) (fmap (fmap Right) t)) x)

instance Functor (U e) where
    fmap f = fold Nil (Tip . f) Bin Let

instance Applicative (U e) where
    pure = Tip
    f <*> x = fold Nil (\w -> fold Nil (Tip . w) Bin Let x) Bin Let f

instance Bifunctor U where
    bimap f g = fold Nil (Tip . g) (Bin . f) Let

instance (Show e, Show a) => Show (U e a) where
    show x = case x of
        Nil -> "Nil"
        Tip x -> "(Tip " ++ show x ++ ")"
        Bin e x y -> "(Bin " ++ show e ++ " " ++ show x ++ " " ++ show y ++ ")"
        Let arr x -> "(Let (" ++ show arr ++ ") " ++ show x ++ ")"

-- Fold with caching of Let subexpressions
foldc :: r -> (a -> r) -> (e -> r -> r -> r) -> U e a -> r
foldc e t b = go
  where
    go x = case x of
      Nil       -> e
      Tip a     -> t a
      Bin e x y -> b e (go x) (go y)
      Let arr x -> let cache = fmap go arr
                   in foldc e (either ((!) cache) t) b x

type Set a = U () a
type Graph a = U Any a

empty :: U e a
empty = Nil

vertex :: a -> U e a
vertex = Tip

edge :: e -> a -> a -> U e a
edge e a b = connect e (vertex a) (vertex b)

overlay :: Monoid e => U e a -> U e a -> U e a
overlay = Bin mempty

connect :: e -> U e a -> U e a -> U e a
connect = Bin

toSet :: U e a -> Set a
toSet = first (const ())

-- compose :: U e a -> U e a -> U e a

-- toGraph :: (Enum a, Bounded a) => U Bool a -> Graph
-- toGraph = undefined

