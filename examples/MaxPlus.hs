module MaxPlus where

-- This is an example of a general construction for lifting united monoids

-- (Z≥0, 0, max, +) is a united monoid:
-- * (0, max) is a commutative monoid
-- * (0, +) is a monoid (also commutative)
-- * + distributes over max, i.e. x + (y `max` z) = (x + y) `max` (x + z)

empty :: Word
empty = 0

overlay :: Word -> Word -> Word
overlay = max

connect :: Word -> Word -> Word
connect = (+)

-- Prime factorisation, padded with zeros to the right:
-- 1 -> []
-- 3 -> [0, 1]
-- 12 -> [2, 1]
type Primes = [Word]

zipWithPadded :: (Word -> Word -> Word) -> Primes -> Primes -> Primes
zipWithPadded f = go
  where
    go xs     []     = [ f x 0 | x <- xs ]
    go []     ys     = [ f 0 y | y <- ys ]
    go (x:xs) (y:ys) = f x y : go xs ys

-- (Z≥1, 1, lcm, *) is a united monoid:
-- * (1, lcm) is a commutative monoid
-- * (1, *) is a monoid (also commutative)
-- * * distributes over lcm, i.e. x * (y `lcm` z) = (x * y) `lcm` (x * z)

-- 1
liftedEmpty :: Primes
liftedEmpty = []

-- lcm
liftedOverlay :: Primes -> Primes -> Primes
liftedOverlay = zipWithPadded overlay

-- multiplication
liftedConnect :: Primes -> Primes -> Primes
liftedConnect = zipWithPadded connect
