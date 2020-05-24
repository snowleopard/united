{-# LANGUAGE FlexibleContexts, FlexibleInstances, QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds, FunctionalDependencies, MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables, EmptyCase, LambdaCase, GADTs, RankNTypes #-}
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

import Control.Applicative
import Data.Array
import Data.Function
import Data.Functor.Identity
import Data.Functor.Product
import Data.Proxy

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
-- | A potentially uncountable collection of tags indexed by values of type @i@.
data Many i a b where
    Many :: i -> Many i a a

------------------------------- Batch type class -------------------------------

-- | Given a product of values tagged by @t@, combine them into the a result.
type Aggregate t a = (forall x. t x -> x) -> a

-- | Generalisation of various abstractions that aggregate multiple effects.
class Batch t f where
    batch :: Aggregate t a -> (forall x. t x -> f x) -> f a

pure_ :: Batch Zero f => a -> f a
pure_ a = batch (const a) (\(x :: Zero a) -> case x of {})

unit :: Batch Zero f => f ()
unit = pure_ ()

fmap_ :: Batch (One a) f => (a -> b) -> f a -> f b
fmap_ f x = batch (\get -> f (get One)) (\One -> x)

liftA2_ :: Batch (Two a b) f => (a -> b -> c) -> f a -> f b -> f c
liftA2_ f x y = batch (\get -> f (get A) (get B)) $ \case { A -> x; B -> y }

apply :: Batch (Two (a -> b) a) f => f (a -> b) -> f a -> f b
apply = liftA2_ ($)

mult :: Batch (Two a b) f => f a -> f b -> f (a, b)
mult = liftA2_ (,)

mfix_ :: Batch (Many a a) f => (a -> f a) -> f a
mfix_ f = batch (\lookup -> fix (lookup . Many)) (\(Many a) -> f a)

-- Type synonyms for classic type classes:
type Pointed_     f = Batch Zero f
type Functor_     f = forall a. Batch (One a) f
type Applicative_ f = forall a b. (Batch Zero f, Batch (One a) f, Batch (Two a b) f)
type Apply_       f = forall a b. (Batch (One a) f, Batch (Two a b) f)
type MonadFix_    f = forall a. Batch (Many a a) f

----------------------------------- Instances ----------------------------------
instance Batch t Identity where
    batch f effects = Identity $ f (runIdentity . effects)

instance Batch t Proxy where
    batch _ _ = Proxy

instance Batch t ((->) env) where
    batch f effects = \env -> f (\t -> effects t env)

instance (Batch t f, Batch t g) => Batch t (Product f g) where
    batch f effects = Pair (batch f $ fst . effects) (batch f $ snd . effects)
      where
        fst (Pair f _) = f
        snd (Pair _ g) = g

-- The 'Maybe' monad is a somewhat less trivial example, which we generalise
-- below to any monad.
instance Batch Zero Maybe where
    batch f _ = Just $ f $ \case {}

instance Batch (One a) Maybe where
    batch f effects = do
        a <- effects One
        return $ f $ \One -> a

instance Batch (Two a b) Maybe where
    batch f effects = do
        a <- effects A
        b <- effects B
        return $ f $ \case { A -> a; B -> b }

-- | Any monad can be given a sequential 'Batch' instance by running the effects
-- in sequence and feeding the results to the aggregation function.
newtype Sequential f a = Sequential { getSequential :: f a }
    deriving (Functor, Applicative, Monad)

instance Monad f => Batch Zero (Sequential f) where
    batch f _ = return $ f $ \case {}

instance Monad f => Batch (One a) (Sequential f) where
    batch f effects = do
        a <- effects One
        return $ f $ \One -> a

instance Monad f => Batch (Two a b) (Sequential f) where
    batch f effects = do
        a <- effects A
        b <- effects B
        return $ f $ \case { A -> a; B -> b }

newtype Cache i a = Cache { getCache :: Array Int a }
    deriving (Functor, Foldable, Traversable)

cache :: (Bounded i, Enum i) => (forall x. Many i a x -> f x) -> Cache i (f a)
cache fs = Cache $ listArray (0, fromEnum top) [ fs (Many i) | i <- all ]
  where
    top = maxBound
    all = [toEnum 0..top]

runCache :: Enum i => ((forall x. Many i a x -> x) -> b) -> Cache i a -> b
runCache f (Cache a) = f (\(Many i) -> a ! fromEnum i)

instance (Monad f, Enum i, Bounded i) => Batch (Many i a) (Sequential f) where
    batch f effects = runCache f <$> sequence (cache effects)

-- | Any applicative functor can be given a parallel 'Batch' instance by running
-- the effects in parallel and feeding the results to the aggregation function.
newtype Parallel f a = Parallel { getParallel :: f a }
    deriving (Functor, Applicative)

instance Applicative f => Batch Zero (Parallel f) where
    batch f _ = pure $ f $ \case {}

instance Applicative f => Batch (One a) (Parallel f) where
    batch f effects = (\a -> f $ \One -> a) <$> effects One

instance Applicative f => Batch (Two a b) (Parallel f) where
    batch f effects =
        liftA2 (\a b -> f $ \case { A -> a; B -> b }) (effects A) (effects B)

instance (Applicative f, Bounded i, Enum i) => Batch (Many i a) (Parallel f) where
    batch f effects = runCache f <$> sequenceA (cache effects)

-- ...
