{-# LANGUAGE FlexibleContexts, FlexibleInstances, QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds, FunctionalDependencies #-}
{-# LANGUAGE DeriveFunctor, EmptyCase, LambdaCase, GADTs, RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module     : Control.Match
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
import Prelude hiding (fmap, pure)
import Data.Void
import Data.Functor.Identity

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

-- | A generalised sum type where @t@ stands for the type of constructor "tags".
-- Each tag has a type parameter @x@ which determines the type of the payload.
data Sigma t a where
    Sigma :: t x -> (x -> a) -> Sigma t a

------------------------------- Match type class -------------------------------
-- | Generalisation of various abstractions that select from multiple effects.
class Match t f where
    match :: (s -> Sigma t a) -> f s -> (forall x. t x -> f x) -> f a

instance Match Zero Identity where
    match f x _ = case f (runIdentity x) of Sigma zero _ -> case zero of {}

instance Match Zero [] where
    match _ _ _ = []

instance Match Zero Maybe where
    match f s _get = case s of
        Nothing -> Nothing
        Just s  -> case f s of Sigma zero _ -> case zero of {}

-- The 0 case is the EmptyCase extension!
-- 0 :: f Void                  * ()        -> f a
-- 1 :: f (i -> a)              * f i       -> f a
-- 2 :: f ((i -> a) + (j -> a)) * f i * f j -> f a
emptyCase :: Match Zero f => f Void -> f a
emptyCase x = match absurd x (\(x :: Zero a) -> case x of {})

apply :: Match (One a) f => f (a -> b) -> f a -> f b
apply f x = match (Sigma One) f (\case One -> x)

branch :: Match (Two (a -> c) (b -> c)) f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch x f g = match toSigma x $ \case
    A -> f
    B -> g
  where
    toSigma (Left  a) = Sigma A ($a)
    toSigma (Right b) = Sigma B ($b)

bind :: Match (Many a b) f => f a -> (a -> f b) -> f b
bind x f = match toSigma x (\(Many x) -> f x)
  where
    toSigma a = Sigma (Many a) id

-- Type synonyms for classic type classes:
-- Stopped working in GHC 8.10?
-- type Selective f = forall a b. (Match Zero f, Match (Two a b) f)
-- type Bind      f = forall a b. Match (Many a b) f
-- type Monad     f = forall a b. (Match Zero f, Match (Many a b) f)

----------------------------------- Instances ----------------------------------

-- ...
