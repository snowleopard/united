{-# LANGUAGE LambdaCase, RankNTypes, TupleSections, TypeOperators #-}
module These where

import Data.Void

data These a b = This a | That b | These a b

these :: (a -> r) -> (b -> r) -> (a -> b -> r) -> These a b -> r
these this that these = \case
    This a    -> this a
    That b    -> that b
    These a b -> these a b

type (:+:) a b = Either a b -- overlay
type (:*:) a b = These a b  -- connect

data Iso a b = Iso { to :: a -> b, from :: b -> a }

leftUnitOverlay :: Iso a (Void :+: a)
leftUnitOverlay = Iso { to = Right, from = either absurd id }

rightUnitOverlay :: Iso a (a :+: Void)
rightUnitOverlay = Iso { to = Left, from = either id absurd }

associativityOverlay :: Iso (a :+: (b :+: c)) ((a :+: b) :+: c)
associativityOverlay = Iso to from
  where
    to = \case
        Left a          -> Left (Left a)
        Right (Left b)  -> Left (Right b)
        Right (Right c) -> Right c
    from = \case
        Left (Left a)  -> Left a
        Left (Right b) -> Right (Left b)
        Right c        -> Right (Right c)

leftUnitConnect :: Iso a (Void :*: a)
leftUnitConnect = Iso { to = That, from = these absurd id absurd }

rightUnitConnect :: Iso a (a :*: Void)
rightUnitConnect = Iso { to = This, from = these id absurd const }

-- 😍
associativityConnect :: Iso (a :*: (b :*: c)) ((a :*: b) :*: c)
associativityConnect = Iso to from
  where
    to = \case
        This a              -> This (This a)
        That (This b)       -> This (That b)
        That (That c)       -> That c
        That (These b c)    -> These (That b) c
        These a (This b)    -> This (These a b)
        These a (That c)    -> These (This a) c
        These a (These b c) -> These (These a b) c
    from = \case
        This (This a)       -> This a
        This (That b)       -> That (This b)
        That c              -> That (That c)
        These (That b) c    -> That (These b c)
        This (These a b)    -> These a (This b)
        These (This a) c    -> These a (That c)
        These (These a b) c -> These a (These b c)

flipEither :: Either a b -> Either b a
flipEither = \case
    Left a  -> Right a
    Right b -> Left b

flipThese :: These a b -> These b a
flipThese = \case
    This a    -> That a
    That b    -> This b
    These a b -> These b a

commutativityOverlay :: Iso (a :+: b) (b :+: a)
commutativityOverlay = Iso { to = flipEither, from = flipEither }

commutativityConnect :: Iso (a :*: b) (b :*: a)
commutativityConnect = Iso { to = flipThese, from = flipThese }

idempotenceOverlay :: Iso a (a :+: a)
idempotenceOverlay = error "Doesn't hold!"

leftDistributivity :: Iso (a :+: (b :*: c)) ((a :*: b) :+: (a :*: c))
leftDistributivity = error "Doesn't hold!"

rightDistributivity :: Iso ((a :*: b) :+: c) ((a :*: c) :+: (b :*: c))
rightDistributivity = error "Doesn't hold!"

----------------------------------- Co-These -----------------------------------

type (:++:) a b = (a, b)
type (:**:) a b = (a, b, Either a b) -- Co-These

leftUnitOverlay2 :: Iso a (() :++: a)
leftUnitOverlay2 = Iso { to = ((),), from = snd }

rightUnitOverlay2 :: Iso a (a :++: ())
rightUnitOverlay2 = Iso { to = (,()), from = fst }

associativityOverlay2 :: Iso (a :++: (b :++: c)) ((a :++: b) :++: c)
associativityOverlay2 = Iso to from
  where
    to   (a, (b, c)) = ((a, b), c)
    from ((a, b), c) = (a, (b, c))

leftUnitConnect2 :: Iso a (() :**: a)
leftUnitConnect2 = error "Doesn't hold!"

rightUnitConnect2 :: Iso a (a :**: ())
rightUnitConnect2 = error "Doesn't hold!"

associativityConnect2 :: Iso (a :**: (b :**: c)) ((a :**: b) :**: c)
associativityConnect2 = error "Doesn't hold!"
