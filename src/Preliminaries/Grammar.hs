{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Preliminaries.Grammar where

import Control.Monad.Bayes.Class
import Control.Monad.Bayes.Inference.MCMC
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Data.Data
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Kind
import Data.MemoTrie
import Data.Tree (Tree (Node, rootLabel))
import Data.Vector hiding (filter, foldM, foldMap, foldl, foldr, length, mapM, replicate, replicateM, sequence, take, zip, (++))
import GHC.Generics
import Preprocessing.MusicTheory
import Text.Printf

type Symbol a = Either (T a) (NT a)

type ShowGrammar a = (Grammar a, Show (NT a), Show (ProdRule a), Show (T a))

class (Eq (NT a), Eq (T a), Eq (ProdRule a), Show (NT a), Show (T a), Show (ProdRule a)) => Grammar a where
  data NT a
  data T a
  data ProdRule a

  -- decode :: Tree (ProdRule a) -> Maybe a
  -- encode :: a -> Tree (ProdRule a)
  -- begin :: Symbol a
  possibleMerges :: [Symbol a] -> [(NT a, ProdRule a)]
  legalRule :: Symbol a -> [ProdRule a]
  nArg :: ProdRule a -> Int
  safeApplyRule :: ProdRule a -> NT a -> Maybe [Symbol a]
  terminate :: ProdRule a

applyRule :: (Show (ProdRule a), Show (NT a), Grammar a) => ProdRule a -> NT a -> [Symbol a]
applyRule x y = case safeApplyRule x y of
  Nothing -> error (printf "wrong type match: cannot apply rule %s to %s" (show x) (show y))
  Just r -> r

nts :: (Enum (NT a), Bounded (NT a)) => [NT a]
nts = enumFrom minBound

rules :: (Enum (ProdRule a), Bounded (ProdRule a)) => [ProdRule a]
rules = enumFrom minBound

mergeRule :: (Grammar a, _) => [Symbol a] -> [(NT a, ProdRule a)]
mergeRule xs = filter (\(x, r) -> safeApplyRule r x == Just xs) [(x, p) | x <- nts, p <- legalRule (Right x)]

-- >>> mergeRule [Left $ NTString]
-- [(NTExpr,RVar)]

-- >>> mergeRule [Right $ TString "x"]
-- [(NTString,RString)]

growTree :: (a -> [a]) -> a -> Tree a
growTree f x = Node x $ growTree f <$> f x

growTreeM :: (Monad m) => (a -> m [a]) -> a -> m (Tree a)
growTreeM sprout seed = do
  branches <- sprout seed
  subtrees <- mapM (growTreeM sprout) branches
  return $ Node seed subtrees

data ParseTree nt r t = Leaf t | Branch nt r [ParseTree nt r t]
  deriving (Show, Eq, Ord)

makeBaseFunctor ''ParseTree

foldParseTree :: (c -> t -> c) -> (c -> nt -> r -> c) -> c -> ParseTree nt r t -> c
foldParseTree f g acc = \case
  Leaf x -> f acc x
  Branch x y ts -> g (foldr (flip $ foldParseTree f g) acc ts) x y

terminals :: ParseTree nt r a -> [a]
terminals = foldParseTree (flip (:)) (\x _ _ -> x) []

-- >>> terminals (Branch (NTChord I I) D5 [Leaf (TChord V I), Leaf (TChord I I)])
-- [TChord V I,TChord I I]

unfoldParseTreeM ::
  (Monad m, ShowGrammar a) =>
  (NT a -> m (ProdRule a)) ->
  Symbol a ->
  m (ParseTree (NT a) (ProdRule a) (T a))
unfoldParseTreeM sampleRule = \case
  Left x -> return $ Leaf x
  Right x -> do
    r <- sampleRule x
    let xs = applyRule r x
    ts <- unfoldParseTreeM sampleRule `mapM` xs
    return $ Branch x r ts

ruleTree :: ParseTree nt r t -> Tree (Maybe r)
ruleTree = \case
  Leaf x -> Node Nothing []
  Branch _ r ts -> Node (Just r) (ruleTree <$> ts)

valTree :: ParseTree (NT a) (ProdRule a) (T a) -> Tree (Symbol a)
valTree = \case
  Leaf x -> Node (Left x) []
  Branch x _ ts -> Node (Right x) (valTree <$> ts)
