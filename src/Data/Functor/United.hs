{-# LANGUAGE GADTs, RankNTypes, TupleSections, TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Functor.United where

import Data.Functor.Identity

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
-- composition :+: and :*: as follows. These alternative definitions reveal the
-- monoidal nature of these abstractions.
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

identityPlus :: Functor f => f :+: Identity ~> f
identityPlus (f :+: Identity k) = k <$> f

identityPlusInv :: f ~> f :+: Identity
identityPlusInv f = f :+: Identity id

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

-------------------------------- :*: is a monoid -------------------------------

identityMult :: Functor f => f :*: Identity ~> f
identityMult (f :*: k) = (runIdentity . k) <$> f

identityMultInv :: f ~> f :*: Identity
identityMultInv f = f :*: pure

associativityMult :: (f :*: g) :*: h ~> f :*: (g :*: h)
associativityMult ((f :*: g) :*: h) = f :*: (\x -> g x :*: h)

------------------------ :+: and :*: are united monoids ------------------------

distributivity :: Applicative f => (f :*: g) :+: (f :*: h) ~> f :*: (g :+: h)
distributivity ((f1 :*: g) :+: (f2 :*: h)) = f :*: (\(x, y) -> g x :+: h y)
  where
    f = (,) <$> f1 <*> f2

containment :: (Applicative f, Functor g) => ((f :*: g) :+: f) a -> (f :*: g) a
containment (fg :+: f) = mapRight identityPlus $ distributivity (fg :+: identityMultInv f)

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
