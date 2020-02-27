{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
module Data.Monoid.United.Language where

import Control.Monad
import Data.Array
import Data.Bifunctor
import Data.Void

data U e a where
    Nil :: U e a
    Tip :: a -> U e a
    Bin :: e -> U e a -> U e a -> U e a
    Let :: (Ix i, Show i) => Array i (U e a) -> U e (Either i a) -> U e a

fold :: forall a b e r. Applicative r
     => (forall x. r x)
     -> (a -> r b)
     -> (forall x. e -> r x -> r x -> r x)
     -> (forall x i. (Ix i, Show i) => Array i (r x) -> r (Either i x) -> r x)
     -> U e a
     -> r b
fold n t b l = go t
  where
    go :: (x -> r y) -> U e x -> r y
    go t x = case x of
      Nil       -> n
      Tip a     -> t a
      Bin e x y -> b e (go t x) (go t y)
      Let arr x -> l (go t <$> arr) (go (either (pure . Left) (fmap Right <$> t)) x)

monofold :: forall a e r. (forall x. r x)
         -> (forall x. x -> r x)
         -> (forall x. e -> r x -> r x -> r x)
         -> (forall x i. (Ix i, Show i) => Array i (r x) -> r (Either i x) -> r x)
         -> U e a
         -> r a
monofold n t b l = go
  where
    go :: U e x -> r x
    go x = case x of
      Nil       -> n
      Tip a     -> t a
      Bin e x y -> b e (go x) (go y)
      Let arr x -> l (fmap go arr) (go x)

instance Functor (U e) where
    fmap f = fold Nil (Tip . f) Bin Let

instance Applicative (U e) where
    pure  = Tip
    (<*>) = ap

instance Monad (U e) where
    return  = Tip
    x >>= f = fold Nil f Bin Let x

instance Bifunctor U where
    bimap f g = fold Nil (Tip . g) (Bin . f) Let

instance (Show e, Show a) => Show (U e a) where
    show x = case x of
        Nil -> "Nil"
        Tip x -> "(Tip " ++ show x ++ ")"
        Bin e x y -> "(Bin " ++ show e ++ " " ++ show x ++ " " ++ show y ++ ")"
        Let arr x -> "(Let (" ++ show arr ++ ") " ++ show x ++ ")"

-- Fold with caching of results for Let subexpressions
foldc :: r -> (a -> r) -> (e -> r -> r -> r) -> U e a -> r
foldc n t b = go
  where
    go x = case x of
      Nil       -> n
      Tip a     -> t a
      Bin e x y -> b e (go x) (go y)
      Let arr x -> let cache = fmap go arr
                   in foldc n (either ((!) cache) t) b x

type Maybe a = U Void a
type Set   a = U ()   a
type Graph a = U Bool a

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

toGraph :: (e -> Bool) -> U e a -> Graph a
toGraph p = first p

size :: U e a -> Int
size = foldc 0 (const 1) (const (+))

hasVertex :: Eq a => a -> U e a -> Bool
hasVertex x = foldc False (==x) (const (||))

induce :: (a -> Bool) -> U e a -> U e a
induce p = fold Nil (\x -> if p x then Tip x else Nil) Bin Let

removeVertex :: Eq a => a -> U e a -> U e a
removeVertex x = induce (/=x)
