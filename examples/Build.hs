{-# LANGUAGE LambdaCase #-}
module Build where

import qualified Data.Set as Set
import Data.Set (Set)

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad

-- Dependency specification
data Spec a = Empty
            | Cycle
            | Task a
            | Sequence (Spec a) (Spec a)
            | Parallel (Spec a) (Spec a)

empty :: Spec a
empty = Empty

overlay :: Spec a -> Spec a -> Spec a
overlay = Parallel

connect :: Spec a -> Spec a -> Spec a
connect = Sequence

zero :: Spec a
zero = Cycle

-- An acyclic dependency graph, or Nothing
type Graph a = Maybe (Map a (Set a))

graph :: Ord a => Spec a -> Graph a
graph = \case
    Empty        -> Just Map.empty
    Cycle        -> Nothing
    Task a       -> Just (Map.singleton a Set.empty)
    Sequence x y -> do
        x <- graph x
        y <- graph y
        let xs = Map.keysSet x
            ys = Map.keysSet y
        guard $ Set.null (Set.intersection xs ys)
        return $ Map.unionsWith Set.union [x, y, Map.fromSet (const ys) xs]
    Parallel x y -> do
        x <- graph x
        y <- graph y
        return $ Map.unionWith Set.union x y

-- A sequence of parallel batches, as in Shake:
-- https://neilmitchell.blogspot.com/2020/11/data-types-for-build-system-dependencies.html
type Batches a = Maybe [Set a]

batches :: Ord a => Spec a -> Batches a
batches = fmap go . graph
  where
    go :: Map a (Set a) -> [Set a]
    go x | Map.null x = []
         | otherwise  = let (batch, rest) = Map.partition Set.null x in
                        Map.keysSet batch : go rest
