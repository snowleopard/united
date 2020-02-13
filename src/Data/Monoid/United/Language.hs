{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}
module Data.Monoid.United.Language where

import Data.Array
import Data.Monoid

data U e a where
    Nil :: U e a
    Tip :: a -> U e a
    Bin :: e -> U e a -> U e a -> U e a
    Let :: Ix i => Array i (U e a) -> U e (Either i a) -> U e a

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

fold :: r -> (a -> r) -> (e -> r -> r -> r) -> U e a -> r
fold e t b = go
  where
    go x = case x of
      Nil       -> e
      Tip a     -> t a
      Bin e x y -> b e (go x) (go y)
      Let arr x -> let cache = fmap go arr
                   in fold e (either ((!) cache) t) b x

toSet :: U e a -> Set a
toSet = fold Nil Tip (const (Bin ()))

-- compose :: U e a -> U e a -> U e a

-- toGraph :: (Enum a, Bounded a) => U Bool a -> Graph
-- toGraph = undefined

