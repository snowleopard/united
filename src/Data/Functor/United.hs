{-# LANGUAGE GADTs, RankNTypes, TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Functor.United where

import Data.Functor.Identity

data (:+:) f g a where
    (:+:) :: f x -> g (x -> a) -> (f :+: g) a

data (:*:) f g a where
    (:*:) :: f x -> (x -> g a) -> (:*:) f g a

instance Functor g => Functor (f :+: g) where
    fmap k (f :+: g) = f :+: (fmap k <$> g)

instance Functor g => Functor (f :*: g) where
    fmap k (f :*: g) = f :*: (fmap k <$> g)

type (~>) f g = forall x. f x -> g x

infixl 1 ~>

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
