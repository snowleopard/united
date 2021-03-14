{-# LANGUAGE RankNTypes #-}
module Function where

import Control.Arrow
import Data.Tuple
import Prelude hiding ((+), (*))

-- This works too:
-- (|||) :: (a -> c) -> (b -> c) -> (Either a b -> c)
(+) :: (a -> b) -> (a -> c) -> (a -> (b, c))
(+) = (&&&)

(*) :: (a -> b) -> (b -> c) -> (a -> c)
(*) = (>>>)

-- The shared unit
empty :: a -> a
empty = id

data Iso a b = Iso { to :: a -> b, from :: b -> a }

leftUnitOverlay :: Iso (a -> b) (a -> (a, b))
leftUnitOverlay = Iso { to = (empty+), from = (snd.) }

rightUnitOverlay :: Iso (a -> b) (a -> (b, a))
rightUnitOverlay = Iso { to = (+empty), from = (fst.) }

leftUnitConnect :: (a -> b) -> a -> b
leftUnitConnect f = empty * f

rightUnitConnect :: (a -> b) -> a -> b
rightUnitConnect f = f * empty

commutativityOverlay :: Iso (a -> (b, c)) (a -> (c, b))
commutativityOverlay = Iso { to = (swap.), from = (swap.) }

-- Here a -> (b, b) must return equal b's, which I can't express in Haskell
idempotenceOverlay :: Iso (a -> b) (a -> (b, b))
idempotenceOverlay = Iso { to = \f -> f + f, from = (fst.) }

(===) :: a -> a -> a
a === _ = a

-- Alas, right distributivity doesn't hold (because + is asymmetric)
leftDistributivity :: (a -> b) -> (b -> c) -> (b -> d) -> a -> (c, d)
leftDistributivity a b c = a * (b + c) === ((a * b) + (a * c))
