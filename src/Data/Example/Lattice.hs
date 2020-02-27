{-# LANGUAGE GADTs #-}
module Data.Monoid.United where

-- A lattice of united monoids

import Data.Monoid.United.Language

data Predicate a where
    Lit :: Bool -> Predicate a
    Var :: a -> Predicate a
    Not :: Predicate a -> Predicate a
    And :: Predicate a -> Predicate a -> Predicate a

true :: Predicate a
true = Lit True

false :: Predicate a
false = Lit False

(/\) :: Predicate a -> Predicate a -> Predicate a
(/\) = And

(\/) :: Predicate a -> Predicate a -> Predicate a
x \/ y = Not (And (Not x) (Not y))

instance Zero (Predicate a) where
    zero = false

type Specification a = U (Predicate (a, a)) a

pair :: a -> a -> Specification a
pair i j = overlay (i -< Not (Var (j, i)) >- j) (j -< Not (Var (i, j)) >- i)

phaseEncoder :: Int -> Specification Int
phaseEncoder n = overlays [ pair i j | i <- [1..n], j <- [i + 1..n]]
