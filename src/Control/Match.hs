{-# LANGUAGE FlexibleContexts, FlexibleInstances, QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds, FunctionalDependencies, MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor, EmptyCase, LambdaCase, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Data.Match
-- Copyright  : (c) Andrey Mokhov 2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- An experiment in expressing Functor, Selective and Monad using the Match
-- type class.
-----------------------------------------------------------------------------
module Control.Match where

import Data.Function
import Data.Functor.Identity
import Prelude hiding (fmap, pure)

------------------------------------- Tags -------------------------------------
-- | A data type defining no tags. Similar to 'Data.Void.Void' but parameterised.
data Zero a where

-- | A data type with a single tag. This data type is commonly known as @Refl@,
-- see "Data.Type.Equality".
data One a b where
    One :: One a a

-- | A data type with two tags 'A' and 'B' that allows us to encode the good old
-- 'Either' as 'Sigma' 'Two', where the tags 'A' and 'B' correspond to 'Left'
-- and 'Right', respectively. See 'eitherToSigma' and 'sigmaToEither' that
-- witness the isomorphism between 'Either' @a b@ and 'Sigma' @(@'Two'@ a b)@.
data Two a b c where
    A :: Two a b a
    B :: Two a b b

-- Interestingly, this matches the type Mono from this blog post:
-- https://elvishjerricco.github.io/2017/03/23/applicative-sorting.html
-- | A potentially uncountable collection of tags.
data Many a b c where
    Many :: a -> Many a b b

------------------------------- Match type class -------------------------------

data Selector f t a where
    Z :: Selector f Zero a
    O :: (x -> a) -> Selector f (One x) a
    S :: (x -> Sigma t a) -> f x -> Selector f t a

-- | Generalisation of various abstractions that select from multiple effects.
class Match t f where
    match :: Selector f t a -> (forall x. t x -> f x) -> f a

empty :: Match Zero f => f a
empty = match Z (\(x :: Zero a) -> case x of {})

fmap :: Match (One a) f => (a -> b) -> f a -> f b
fmap f x = match (O f) (\One -> x)

branch :: Match (Two (a -> c) (b -> c)) f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x f g = match (S toSigma x) $ \case
    A -> f
    B -> g
  where
    toSigma (Left  a) = Sigma A ($a)
    toSigma (Right b) = Sigma B ($b)

bind :: Match (Many a b) f => f a -> (a -> f b) -> f b
bind x f = match (S toSigma x) (\(Many x) -> f x)
  where
    toSigma a = Sigma (Many a) id

-- Type synonyms for classic type classes:
type MonadZero f = Match Zero f
type Functor   f = forall a. Match (One a) f
type Selective f = forall a b. (Match Zero f, Match (Two a b) f)
type Bind      f = forall a b. Match (Many a b) f
type Monad     f = forall a b. (Match Zero f, Match (Many a b) f)

-- Constrained versions of type classes, e.g. for "Data.Set".
type FunctorOrd f = forall a. (Ord a, Match (One a) f)
type MonadOrd   f = forall a b. (Ord a, Ord b, Match Zero f, Match (Many a b) f)

----------------------------------- Instances ----------------------------------

-- ...
