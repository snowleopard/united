{-# LANGUAGE GADTs, RankNTypes, TupleSections, TypeOperators #-}
module Sketch where

import Data.Bifunctor
import Data.Functor.Identity
import Data.Void

-- Two ways of composing functors, whose definitions mirror the type signatures
-- of the Applicative's (<*>) and Monad's (>>=) operators.
-- Inspired by these awesome blog posts by Bartosz Milewski and Oleg Grenrus:
-- https://bartoszmilewski.com/2018/02/17/free-monoidal-functors/
-- http://oleg.fi/gists/posts/2018-02-21-single-free.html
data (:+:) f g a where
    (:+:) :: f x -> g (x -> a) -> (f :+: g) a

data (:*:) f g a where
    (:*:) :: f x -> (x -> g a) -> (:*:) f g a

instance Functor g => Functor (f :+: g) where
    fmap k (f :+: g) = f :+: (fmap k <$> g)

instance Functor g => Functor (f :*: g) where
    fmap k (f :*: g) = f :*: (fmap k <$> g)

-- A convenient alias for natural tranformations.
type (~>) f g = forall x. f x -> g x

infixl 1 ~>

-- Standard Applicative and Monad type classes can be defined via functor
-- composition :+: and :*: as follows. These definitions may seem strange at
-- first, but if you inline :+: and :*: you will see that we simply pack the two
-- arguments to (<*>) and (>>=) into the two product types, and use ~> to hide
-- the underlying type a. These alternative definitions make the monoidal nature
-- of Applicative and Monad abstractions more apparent.
class Functor f => Applicative' f where
    pure' :: Identity ~> f
    ap'   :: f :+: f  ~> f

class Applicative f => Monad' f where
    return' :: Identity ~> f
    bind'   :: f :*: f  ~> f

--------------------------------------------------------------------------------
-- Below is a draft justification for the following two statements:
--
--  Applicative and Monad are united monoids in the category of endofunctors.
--
--  Applicative and Monad are algebraic graphs in the category of endofunctors.
--------------------------------------------------------------------------------

-------------------- :+: is an idempotent commutative monoid -------------------

rightIdentityPlus :: Functor f => f :+: Identity ~> f
rightIdentityPlus (f :+: Identity k) = k <$> f

rightIdentityPlusInv :: f ~> f :+: Identity
rightIdentityPlusInv f = f :+: Identity id

leftIdentityPlus :: Functor f => Identity :+: f ~> f
leftIdentityPlus = rightIdentityPlus . commutativityPlus

leftIdentityPlusInv :: Functor f => f ~> Identity :+: f
leftIdentityPlusInv = commutativityPlus . rightIdentityPlusInv

associativityPlus :: Functor h => (f :+: g) :+: h ~> f :+: (g :+: h)
associativityPlus ((f :+: g) :+: h) = f :+: (g :+: fmap (.) h)

associativityPlusInv :: (Functor g, Functor h) => f :+: (g :+: h) ~> (f :+: g) :+: h
associativityPlusInv (f :+: (g :+: h)) = (f :+: fmap (,) g) :+: fmap uncurry h

commutativityPlus :: Functor f => f :+: g ~> g :+: f
commutativityPlus (f :+: g) = g :+: (flip ($) <$> f)

idempotencePlus :: Applicative f => f ~> f :+: f
idempotencePlus f = f :+: pure id

idempotencePlusInv :: Applicative f => f :+: f ~> f
idempotencePlusInv (f1 :+: f2) = f2 <*> f1

-------------------------- :*: is an idempotent monoid -------------------------

leftIdentityMult :: Identity :*: f ~> f
leftIdentityMult (k :*: f) = f (runIdentity k)

leftIdentityMultInv :: f ~> Identity :*: f
leftIdentityMultInv f = pure () :*: const f

rightIdentityMult :: Functor f => f :*: Identity ~> f
rightIdentityMult (f :*: k) = runIdentity . k <$> f

rightIdentityMultInv :: f ~> f :*: Identity
rightIdentityMultInv f = f :*: pure

associativityMult :: (f :*: g) :*: h ~> f :*: (g :*: h)
associativityMult ((f :*: g) :*: h) = f :*: (\x -> g x :*: h)

associativityMultInv :: Applicative g => f :*: (g :*: h) ~> (f :*: g) :*: h
associativityMultInv (f :*: gh) = (f :*: (k . gh)) :*: id
  where
    k (g :*: h) = fmap h g

idempotenceMult :: Applicative f => f ~> f :*: f
idempotenceMult f = pure () :*: const f

idempotenceMultInv :: Monad f => f :*: f ~> f
idempotenceMultInv (f1 :*: f2) = f1 >>= f2

------------------------ :+: and :*: are united monoids ------------------------

leftDistributivity :: Applicative f => (f :*: g) :+: (f :*: h) ~> f :*: (g :+: h)
leftDistributivity ((f1 :*: g) :+: (f2 :*: h)) = f :*: (\(x, y) -> g x :+: h y)
  where
    f = (,) <$> f1 <*> f2

-- Could do with representable functors.
leftDistributivityInv :: f :*: (g :+: h) ~> (f :*: g) :+: (f :*: h)
leftDistributivityInv = error "TODO"

rightDistributivity :: (Functor g, Applicative h) => (f :*: h) :+: (g :*: h) ~> (f :+: g) :*: h
rightDistributivity ((f :*: h1) :+: (g :*: h2)) = (f :+: (flip (,) <$> g)) :*: h
  where
    h (i, j) = (flip ($) <$> h1 i) <*> h2 j

-- Could do with representable functors.
rightDistributivityInv :: (f :+: g) :*: h ~> (f :*: h) :+: (g :*: h)
rightDistributivityInv = error "TODO"

leftContainment :: (Applicative f, Functor g) => (f :*: g) :+: f ~> f :*: g
leftContainment (fg :+: f) = mapRight rightIdentityPlus $
    leftDistributivity (fg :+: rightIdentityMultInv f)

rightContainment :: (Functor f, Applicative g) => (f :*: g) :+: g ~> f :*: g
rightContainment (fg :+: g) = mapLeft rightIdentityPlus $
    rightDistributivity (fg :+: leftIdentityMultInv g)

leftContainmentInv :: f :*: g ~> (f :*: g) :+: f
leftContainmentInv = error "TODO"

rightContainmentInv :: f :*: g ~> (f :*: g) :+: g
rightContainmentInv = error "TODO"

mapLeft :: (f ~> g) -> f :*: h ~> g :*: h
mapLeft fg (f :*: h) = fg f :*: h

mapRight :: (g ~> h) -> f :*: g ~> f :*: h
mapRight gh (f :*: g) = f :*: fmap gh g

------------------------------- Algebraic graphs -------------------------------

decomposition :: (Applicative f, Applicative g, Applicative h)
    => (f :*: g) :+: (f :*: h) :+: (g :*: h) ~> (f :*: g) :*: h
decomposition ((f1 :*: g1) :+: (f2 :*: h1) :+: (g2 :*: h2)) =
    (f :*: uncurry g) :*: (\(x, k, j) -> h x k j)
  where
    f       = (,)              <$> f1    <*> f2
    g i j   = (,,j)            <$> g1 i  <*> g2
    h x k j = (flip ($) . ($x) <$> h1 j) <*> h2 k

decompositionInv :: (f :*: g) :*: h ~> (f :*: g) :+: (f :*: h) :+: (g :*: h)
decompositionInv = error "TODO"

--------------------------------------------------------------------------------

-- Proofs of isomorphism between functions (a -> b) and polymorphic expressions
-- like:
--
--    forall f . Functor f     => f a -> f b
--    forall f . Applicative f => f a -> f b
--
-- See this ICFP'18 paper by Guillaume Boisseau and Jeremy Gibbons for more details:
-- https://icfp18.sigplan.org/event/icfp-2018-papers-what-you-needa-know-about-yoneda

fromFun :: (a -> b) -> (forall f . Functor f => f a -> f b)
fromFun f x = f <$> x

toFun :: (forall f . Functor f => f a -> f b) -> (a -> b)
toFun h = runIdentity . h . Identity

-------------------------------------- Day -------------------------------------

data Day f g a where
    Day :: f x -> g y -> (x -> y -> a) -> Day f g a

toDay :: (f :+: g) a -> Day f g a
toDay (f :+: g) = Day f g (flip ($))

fromDay :: Functor g => Day f g a -> (f :+: g) a
fromDay (Day f g k) = f :+: (flip k <$> g)

------------------------------ Selective functors ------------------------------
data (:|:) f g a where
    (:|:) :: f (Either x a) -> g (x -> a) -> (:|:) f g a

class Applicative f => Selective f where
    select :: f (Either a b) -> f (a -> b) -> f b

leftIdentitySelect :: Selective f => Identity :|: f ~> f
leftIdentitySelect ((Identity (Left  x)) :|: f) = ($x) <$> f
leftIdentitySelect ((Identity (Right a)) :|: _) = pure a

leftIdentitySelectInv :: Applicative f => f ~> Identity :|: f
leftIdentitySelectInv f = pure (Left ()) :|: (const <$> f)

rightIdentitySelect :: Functor f => f :|: Identity ~> f
rightIdentitySelect (f :|: k) = either (runIdentity k) id <$> f

rightIdentitySelectInv :: Applicative f => f ~> f :|: Identity
rightIdentitySelectInv f = (Right <$> f) :|: pure absurd

associativitySelect :: (Functor f, Functor g, Functor h) => f :|: (g :|: h) ~> (f :|: g) :|: h
associativitySelect (f :|: (g :|: h)) = ((p <$> f) :|: (q <$> g)) :|: (r <$> h)
  where
    p x = Right <$> x
    q y = \a -> bimap (,a) ($a) y
    r z = uncurry z
