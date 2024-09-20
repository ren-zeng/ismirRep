{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SemiringParsing where

import CYKParser
import Control.Arrow (Arrow (first))
import Control.Monad
import Data.Function (fix)
import Data.Maybe (catMaybes, mapMaybe)
import Data.MemoTrie
import Data.Semiring
import GHC.Generics (Generic)
import Grammar hiding (Plus)
import PCFG
import SLG
import TemplateGrammar
import Prelude hiding (product, sum, (*), (+))

data SemiringOver a = SemiringOver
  { zeroS :: a,
    oneS :: a,
    plusS :: a -> a -> a,
    timesS :: a -> a -> a
  }

sumS :: (Foldable t) => SemiringOver a -> t a -> a
sumS sr = foldr (plusS sr) (zeroS sr)

productS :: (Foldable t) => SemiringOver a -> t a -> a
productS sr = foldr (timesS sr) (oneS sr)

data FreeSemiring a
  = Val a
  | Plus (FreeSemiring a) (FreeSemiring a)
  | Times (FreeSemiring a) (FreeSemiring a)
  | One
  | Zero
  deriving (Functor, Eq, Show)

instance Semiring (FreeSemiring a) where
  plus = Plus
  times = Times
  zero = Zero
  one = One

simpl :: FreeSemiring a -> FreeSemiring a
simpl (Plus x Zero) = simpl x
simpl (Plus Zero x) = simpl x
simpl (Times One x) = simpl x
simpl (Times x One) = simpl x
simpl x = x

data SemiRingOperator = NPlus | NTimes

semiringTree :: FreeSemiring a -> ParseTree a SemiRingOperator a
semiringTree = undefined

evalSemiring :: (Semiring a) => FreeSemiring a -> a
evalSemiring = \case
  Val x -> x
  Zero -> zero
  One -> one
  Plus x y -> plus (evalSemiring x) (evalSemiring y)
  Times x y -> times (evalSemiring x) (evalSemiring y)

-------------------------------------------------------
-- CYK algorithm that is polymorphic over a semiring --
-------------------------------------------------------

-- | CYK algorithm with an implicit semiring
cykSemiring :: (Semiring b, Eq b) => ([a] -> b) -> [a] -> b
cykSemiring f sur
  | f sur == zero = sum [cykSemiring f l * cykSemiring f r | (l, r) <- splits sur]
  | otherwise = f sur

-- | CYK algorithm with an explicit semiring
cykSemiringOver :: (Eq b) => SemiringOver b -> ([a] -> b) -> [a] -> b
cykSemiringOver sr f sur
  | f sur == zeroS sr =
      foldr
        (plusS sr)
        (zeroS sr)
        [timesS sr (cykSemiringOver sr f l) (cykSemiringOver sr f r) | (l, r) <- splits sur]
  | otherwise = f sur

--------------------------------
-- Derivation Forest Semiring --
--------------------------------

-- | The semiring over derivation forests.
--
-- @0 = {}@
--
-- @1 = {TrivialDerivation}@
--
-- @f1 ⊕ f2 = f1 ∪ f2@
--
-- @f1 ⊗ f2 = {m | m ∈ merges t1 t2, t1 ∈ f1, t2 ∈ f2}@
derivationForestSemiring :: (Grammar a) => SemiringOver [Derivation a]
derivationForestSemiring =
  SemiringOver
    { zeroS = [],
      oneS = [Derivation Nothing],
      plusS = (++),
      timesS = \ts1 ts2 -> do
        Derivation t1 <- ts1
        Derivation t2 <- ts2
        let f a b = case (a, b) of
              (Just x, Just y) -> Just <$> mergePTree [x, y]
              (Just x, Nothing) -> Just <$> mergePTree [x]
              (Nothing, Just y) -> Just <$> mergePTree [y]
              (Nothing, Nothing) -> []
        Derivation <$> f t1 t2
    }

derivationForest :: (Grammar a, Eq (Derivation a)) => [T a] -> [Derivation a]
derivationForest = cykSemiring (fmap fromParseTree . directMerge)

newtype Derivation a = Derivation (Maybe (ParseTree (NT a) (ProdRule a) (T a)))

deriving instance (Grammar a) => Eq (Derivation a)

deriving instance (Grammar a) => Show (Derivation a)

fromParseTree :: ParseTree (NT a) (ProdRule a) (T a) -> Derivation a
fromParseTree = Derivation . Just

instance (Grammar a) => Semiring [Derivation a] where
  plus = plusS derivationForestSemiring
  times = timesS derivationForestSemiring
  zero = zeroS derivationForestSemiring
  one = oneS derivationForestSemiring

--------------------------------------
-- Derivation Distribution Semiring --
--------------------------------------

-- | A family of semirings over weighted derivation forest @(Derivation, P (der | ruleProb))@.
-- The family is indexed by functions @ruleProb :: (NT a -> ProdRule a -> Double)@.
--
-- @0 = {}@
--
-- @1 = {(TrivialDerivation,1)}@
--
-- @f1 ⊕ f2 = f1 ∪ f2@
--
-- @f1 ⊗ f2 = {(m,p * p1 * p2) | (m,p) ∈ mergesWithProb t1 t2, (t1,p1) ∈ f1, (t2,p2) ∈ f2}@
derDistrSemiring ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  SemiringOver [(Derivation a, Double)]
derDistrSemiring ruleProb =
  SemiringOver
    { zeroS = [],
      oneS = [(Derivation Nothing, 1)],
      plusS = (++),
      timesS = \x y -> do
        d1 <- x
        d2 <- y
        mergeDerDistr ruleProb [d1, d2]
    }

derivationDistribution ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  [T a] ->
  [(Derivation a, Double)]
derivationDistribution ruleProb =
  cykSemiringOver
    (derDistrSemiring ruleProb)
    (fmap (first fromParseTree) . directMergeProb ruleProb)

mergeParseTreeDistr ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  [(ParseTree (NT a) (ProdRule a) (T a), Double)] ->
  [(ParseTree (NT a) (ProdRule a) (T a), Double)]
mergeParseTreeDistr f wts =
  let ts = fst <$> wts
   in case (possibleMerges . fmap topSymbol) (fst <$> wts) of
        [] -> []
        ms -> [(Branch nt r ts, f nt r * product (snd <$> wts)) | (nt, r) <- ms]

unDerivation :: Derivation a -> Maybe (ParseTree (NT a) (ProdRule a) (T a))
unDerivation (Derivation x) = x

mergeDerDistr ::
  (Grammar a) =>
  (NT a -> ProdRule a -> Double) ->
  [(Derivation a, Double)] ->
  [(Derivation a, Double)]
mergeDerDistr ruleProb derDist = (\(t, s) -> (Derivation (Just t), s)) <$> mergeParseTreeDistr ruleProb tDist
  where
    tDist = [(t, p) | (Derivation (Just t), p) <- derDist]

defaultProb :: NT Chord -> ProdRule Chord -> Double
defaultProb (NTChord x y) r = case x of
  V -> case r of
    RChord -> 0.5
    RProl -> 0.2
    RAppD -> 0.1
    RD5 -> 0.1
    RIV_V -> 0.1
  _ -> case r of
    RChord -> 0.5
    RProl -> 0.2
    RAppD -> 0.1
    RD5 -> 0.2
    RIV_V -> 0

-- >>>  derivationDistribution defaultProb testSurface
-- [(Derivation (Just (Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RChord [Leaf (TChord IV I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RChord [Leaf (TChord I I)]]])),2.5000000000000006e-4),(Derivation (Just (Branch (NTChord I I) RD5 [Branch (NTChord V I) RIV_V [Branch (NTChord IV I) RD5 [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord IV I) RChord [Leaf (TChord IV I)]],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RChord [Leaf (TChord I I)]])),2.5000000000000006e-4)]

testSurface = zipWith TChord [I, IV, V, I] (replicate 4 I)

-- >>> length $ derivationForest  testSurface
-- 2

-----------------------------
-- Template Semiring (New) --
-----------------------------

-- | The semiring over the set of template of a grammar.
--
-- @0 = {}@
--
-- @1 = {TrivialTemplate}@
--
-- @f1 ⊕ f2 = f1 ∪ f2@
--
-- @f1 ⊗ f2 = {m | m ∈ mergeTemplate [t1, t2], t1 ∈ f1, t2 ∈ f2}@
slgSemiring :: (_) => SemiringOver (SLG k f a)
slgSemiring =
  SemiringOver
    { zeroS = SLG zero mempty,
      oneS = SLG one mempty,
      plusS = \s1 s2 -> SLG (liftA2 (+) (start s1) (start s2)) (bindings s1 <> bindings s2),
      timesS = \s1 s2 -> SLG (liftA2 (*) (start s1) (start s2)) (bindings s1 <> bindings s2)
    }
