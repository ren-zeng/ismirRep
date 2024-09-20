{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module CYKParser where

import Control.Arrow
import Data.Function
import Data.List (inits, tails)
import Data.List.Extra (notNull)
import Data.List.NonEmpty (nonEmpty)
import Data.MemoTrie
import Data.Semiring
import Data.Tree
import GHC.Generics
import Grammar

-- >>>   head  $ parseCYK $ fmap (\x->TChord x I) $ (concat . replicate 2) [I,IV,V,I,I,II,V,I,IV,V,I]
-- Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RChord [Leaf (TChord IV I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RD5 [Branch (NTChord II I) RChord [Leaf (TChord II I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RChord [Leaf (TChord IV I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RChord [Leaf (TChord IV I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RD5 [Branch (NTChord II I) RChord [Leaf (TChord II I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RChord [Leaf (TChord IV I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RChord [Leaf (TChord I I)]]]]]]]]]]]]]]]]

parseCYK ::
  (HasTrie (T a), Grammar a) =>
  [T a] ->
  [ParseTree (NT a) (ProdRule a) (T a)]
parseCYK sur = memoFix parseCYK' sur

parseCYK' ::
  (Grammar a) =>
  ([T a] -> [ParseTree (NT a) (ProdRule a) (T a)]) ->
  ([T a] -> [ParseTree (NT a) (ProdRule a) (T a)])
parseCYK' f [] = []
parseCYK' f sur =
  case possibleMerges (Left <$> sur) of
    [] -> do
      (l, r) <- splits sur
      treeL <- f l
      treeR <- f r
      mergePTree [treeL, treeR]
    merges -> do
      (root, p) <- merges
      return $ Branch root p (Leaf <$> sur)

directMerge :: (Grammar a) => [T a] -> [ParseTree (NT a) (ProdRule a) (T a)]
directMerge sur = do
  (root, rule) <- possibleMerges (Left <$> sur)
  return $ Branch root rule (Leaf <$> sur)

directMergeProb ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  [T a] ->
  [(ParseTree (NT a) (ProdRule a) (T a), Double)]
directMergeProb ruleProb sur = do
  merges <- possibleMerges (Left <$> sur)
  let (root, p) = merges
  return $ (Branch root p (Leaf <$> sur), ruleProb root p)

topSymbol :: ParseTree b r a -> Either a b
topSymbol = \case
  Leaf x -> Left x
  Branch x _ _ -> Right x

mergePTree :: (_) => [ParseTree (NT a) (ProdRule a) (T a)] -> [ParseTree (NT a) (ProdRule a) (T a)]
mergePTree xs = do
  (root, p) <- possibleMerges $ topSymbol <$> xs
  return $ Branch root p xs

splits :: [a] -> [([a], [a])]
splits xs = filter (\(a, b) -> notNull a && notNull b) $ zip (inits xs) (tails xs)
