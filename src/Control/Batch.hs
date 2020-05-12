{-# LANGUAGE FlexibleContexts, FlexibleInstances, QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds, FunctionalDependencies, MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor, EmptyCase, LambdaCase, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Batch
-- Copyright  : (c) Andrey Mokhov 2020
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- An experiment in expressing Functor, Applicative and MonadFix using the Batch
-- type class.
-----------------------------------------------------------------------------
module Control.Batch where

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

------------------------------- Batch type class -------------------------------

-- | Given a product of values tagged by @t@, combine them into the a result.
type Aggregate t a = (forall x. t x -> x) -> a

-- | Generalisation of various abstractions that aggregate multiple effects.
class Batch t f where
    batch :: Aggregate t a -> (forall x. t x -> f x) -> f a

pure :: Batch Zero f => a -> f a
pure a = batch (const a) (\(x :: Zero a) -> case x of {})

unit :: Batch Zero f => f ()
unit = pure ()

fmap :: Batch (One a) f => (a -> b) -> f a -> f b
fmap f x = batch (\get -> f (get One)) (\One -> x)

liftA2 :: Batch (Two a b) f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x y = batch (\get -> f (get A) (get B)) $ \case { A -> x; B -> y }

(<*>) :: Batch (Two (a -> b) a) f => f (a -> b) -> f a -> f b
(<*>) = liftA2 ($)

mult :: Batch (Two a b) f => f a -> f b -> f (a, b)
mult = liftA2 (,)

mfix :: Batch (Many a a) f => (a -> f a) -> f a
mfix f = batch (\lookup -> fix (lookup . Many)) (\(Many a) -> f a)

-- Type synonyms for classic type classes:
type Pointed     f = Batch Zero f
type Functor     f = forall a. Batch (One a) f
type Applicative f = forall a b. (Batch Zero f, Batch (Two a b) f)
type Apply       f = forall a b. Batch (Two a b) f
type MonadFix    f = forall a. Batch (Many a a) f

-- Constrained versions of type classes, e.g. for "Data.Set".
type FunctorOrd     f = forall a. (Ord a, Batch (One a) f)
type ApplicativeOrd f = forall a b. (Ord a, Ord b, Batch Zero f, Batch (Two a b) f)

----------------------------------- Instances ----------------------------------
instance Batch t Identity where
    batch f xs = Identity $ f (runIdentity . xs)

-- ...
