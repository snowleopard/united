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
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Maybe
import Data.Monoid hiding (Product)
import Data.Proxy
import Prelude hiding (foldMap)

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

-- Interestingly, this matches the type 'Mono' from this blog post:
-- https://elvishjerricco.github.io/2017/03/23/applicative-sorting.html
-- | A potentially uncountable collection of tags indexed by values of type @i@.
data Many i a b where
    Many :: i -> Many i a a

-- | An equivalent of 'Foldable' for @t@-shaped containers.
class Fold t where
    fold :: Monoid m => (forall x. t x -> m) -> m

instance Fold Zero where
    fold _ = mempty

instance Fold (One a) where
    fold get = get One

instance Fold (Two a b) where
    fold get = get A <> get B

instance Enum i => Fold (Many i a) where
    fold get = mconcat [ get (Many i) | i <- enumFrom (toEnum 0) ]

foldMap :: (Fold t, Monoid m) => (a -> m) -> (forall x. t x -> a) -> m
foldMap f get = fold (f . get)

toList :: Fold t => (forall x. t x -> a) -> [a]
toList = foldMap pure

toListN :: Fold t => (forall x. t x -> a) -> ([a], Int)
toListN get = getSum <$> foldMap (\a -> ([a], Sum 1)) get

newtype Cache i a = Cache { getCache :: Array Int a }
    deriving (Functor, Foldable, Traversable)

cache :: Enum i => (forall x. Many i a x -> f x) -> Cache i (f a)
cache effects = Cache $ listArray (0, len - 1) all
  where
    (all, len) = toListN (mono effects)
    mono :: (forall x. Many i a x -> f x) -> (forall x. Many i a x -> f a)
    mono get (Many i) = get (Many i)

runCache :: Enum i => ((forall x. Many i a x -> x) -> b) -> Cache i a -> b
runCache f (Cache a) = f (\(Many i) -> a ! fromEnum i)

------------------------------- Batch type class -------------------------------

-- | Generalisation of various abstractions that aggregate multiple effects.
class Batch t f where
    batch :: ((forall x. t x -> x) -> a) -> (forall x. t x -> f x) -> f a

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
-- Stopped working in GHC 8.10?
-- type Pointed     f = Batch Zero f
-- type Functor     f = forall a. Batch (One a) f
-- type Applicative f = forall a b. (Batch Zero f, Batch (One a) f, Batch (Two a b) f)
-- type Apply       f = forall a b. (Batch (One a) f, Batch (Two a b) f)
-- type MonadFix    f = forall a. Batch (Many a a) f

----------------------------------- Instances ----------------------------------
instance Batch t Proxy where
    batch _ _ = Proxy

instance Batch t Identity where
    batch f effects = Identity $ f (runIdentity . effects)

instance Batch t ((->) env) where
    batch f effects = \env -> f (`effects` env)

instance (Batch t f, Batch t g) => Batch t (Product f g) where
    batch f effects = Pair (batch f $ fst . effects) (batch f $ snd . effects)
      where
        fst (Pair f _) = f
        snd (Pair _ g) = g

instance (Fold t, Monoid m) => Batch t (Const m) where
    batch _ effects = Const $ fold (getConst . effects)

-- Write: a Product of Const and Identity.
instance (Fold t, Monoid m) => Batch t ((,) m) where
    batch f effects = (fold (fst . effects), f (snd . effects))

-- TODO: Get rid of the unsafe 'fromJust'
instance Fold t => Batch t Maybe where
    batch f effects = case fold (All . isJust . effects) of
        All True  -> Just $ f (fromJust . effects)
        All False -> Nothing

data Wrapped t w a where
    W :: t x -> Wrapped t w (w x)

instance (Batch (Wrapped t g) f, Batch t g) => Batch t (Compose f g) where
    batch f effects = Compose $ batch (\get -> batch f (get . W)) wrapped
      where
        wrapped :: forall x. Wrapped t g x -> f x
        wrapped (W t) = getCompose (effects t)

instance Fold t => Batch t ZipList where
    batch f effects = case batch f heads of
        Nothing -> ZipList []
        Just x  -> ZipList $ x : getZipList (batch f tails)
      where
        heads :: forall x. t x -> Maybe x
        heads t = case effects t of
            ZipList []    -> Nothing
            ZipList (x:_) -> Just x
        tails :: forall x. t x -> ZipList x
        tails t = case effects t of
            ZipList []     -> ZipList []
            ZipList (_:xs) -> ZipList xs

data Lift f a = Pure a | Other (f a)

runLift :: (a -> r) -> (f a -> r) -> Lift f a -> r
runLift pure other = \case { Pure a -> pure a; Other x -> other x }

-- Maybe-like
instance (Batch Zero f, Batch t f, Fold t) => Batch t (Lift f) where
    batch f effects = case fold (All . isPure . effects) of
        All True  -> Pure $ f (fromPure . effects)
        All False -> Other $ batch f (unLift . effects)
      where
        isPure   = runLift (const True) (const False)
        fromPure = runLift id (error "impossible")
        unLift   = runLift pure_ id

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

instance (Monad f, Enum i) => Batch (Many i a) (Sequential f) where
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

instance (Applicative f, Enum i) => Batch (Many i a) (Parallel f) where
    batch f effects = runCache f <$> sequenceA (cache effects)

-- ...
