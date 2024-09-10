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
import Data.List (inits, tails)
import Data.List.Extra (notNull)
import Data.List.NonEmpty (nonEmpty)
import Data.MemoTrie
import Data.Semiring
import Data.Tree
import GHC.Generics
import Grammar

-- >>>  length (parseCYK $ Right . uncurry TChord <$> [(V,V`Of`I),(V,I), (I,I)])
-- 1
deriving instance Generic (T (Chord x y))

deriving instance Generic (Numeral)

instance HasTrie (T (Chord x y)) where
  newtype T (Chord x y) :->: b = ChordTrie {unChordTrie :: Reg (T (Chord x y)) :->: b}
  trie = trieGeneric ChordTrie
  untrie = untrieGeneric unChordTrie
  enumerate = enumerateGeneric unChordTrie

instance HasTrie (Numeral) where
  newtype (Numeral) :->: b = NumeralTrie {unNumeralTrie :: Reg (Numeral) :->: b}
  trie = trieGeneric NumeralTrie
  untrie = untrieGeneric unNumeralTrie
  enumerate = enumerateGeneric unNumeralTrie

parseCYK' ::
  (Grammar a) =>
  ([T a] -> [ParseTree (NT a) (ProdRule a) (T a)]) ->
  ([T a] -> [ParseTree (NT a) (ProdRule a) (T a)])
parseCYK' oneStep [] = []
parseCYK' oneStep sur =
  case possibleMerges (Left <$> sur) of
    [] -> do
      (l, r) <- splits sur
      treeL <- oneStep l
      treeR <- oneStep r
      mergePTree [treeL, treeR]
    merges -> do
      (root, p) <- merges
      return $ Branch root p (Leaf <$> sur)

directMerge :: (Grammar a) => [T a] -> [ParseTree (NT a) (ProdRule a) (T a)]
directMerge sur = do
  merges <- possibleMerges (Left <$> sur)
  let (root, p) = merges
  return $ Branch root p (Leaf <$> sur)

directMergeProb ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  [T a] ->
  [(ParseTree (NT a) (ProdRule a) (T a), Double)]
directMergeProb ruleProb sur = do
  merges <- possibleMerges (Left <$> sur)
  let (root, p) = merges
  return $ (Branch root p (Leaf <$> sur), ruleProb root p)

parseCYK ::
  (HasTrie (T a), Grammar a) =>
  [T a] ->
  [ParseTree (NT a) (ProdRule a) (T a)]
parseCYK = memoFix parseCYK'

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
