{-# LANGUAGE GADTs #-}
module Data.Monoid.United.Language where

import Control.Monad
import Data.Bifunctor
import Data.Void
import Prelude hiding ((<>))

class Monoid a where
    unit :: a
    (<>) :: a -> a -> a

class Zero a where
    zero :: a

class IsZero a where
    isZero :: a -> Bool

data U e a where
    Nil :: U e a
    Tip :: a -> U e a
    Bin :: e -> U e a -> U e a -> U e a

type Maybe a = U Void a
type Set   a = U ()   a
type Graph a = U Bool a

empty :: U e a
empty = Nil

vertex :: a -> U e a
vertex = Tip

overlay :: Zero e => U e a -> U e a -> U e a
overlay = Bin zero

connect :: e -> U e a -> U e a -> U e a
connect = Bin

edge :: e -> a -> a -> U e a
edge e x y = connect e (vertex x) (vertex y)

(-<) :: a -> e -> (a, e)
g -< e = (g, e)

(>-) :: (a, e) -> a -> U e a
(x, e) >- y = edge e x y

overlays :: Zero e => [U e a] -> U e a
overlays = foldr overlay empty

connects :: Zero e => [U e a] -> U e a
connects = foldr overlay empty

fold :: r -> (a -> r) -> (e -> r -> r -> r) -> U e a -> r
fold n t b = go
  where
    go x = case x of
      Nil       -> n
      Tip a     -> t a
      Bin e x y -> b e (go x) (go y)

instance Functor (U e) where
    fmap f = fold Nil (Tip . f) Bin

instance Applicative (U e) where
    pure  = Tip
    (<*>) = ap

instance Monad (U e) where
    x >>= f = fold Nil f Bin x

instance Bifunctor U where
    bimap f g = fold Nil (Tip . g) (Bin . f)

toSet :: U e a -> Set a
toSet = first (const ())

toGraph :: (e -> Bool) -> U e a -> Graph a
toGraph = first

size :: U e a -> Int
size = fold 0 (const 1) (const (+))

hasVertex :: Eq a => a -> U e a -> Bool
hasVertex x = fold False (==x) (const (||))

induce :: (a -> Bool) -> U e a -> U e a
induce p = fold Nil (\x -> if p x then Tip x else Nil) Bin

removeVertex :: Eq a => a -> U e a -> U e a
removeVertex x = induce (/=x)
