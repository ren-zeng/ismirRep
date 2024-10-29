{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module GrammarInstances where

import Data.MemoTrie
import Data.Tree
import GHC.Generics
import Preliminaries.Grammar

data Expr
  = Var String
  | Const Int
  | Expr `Plus` Expr
  | Expr `Mult` Expr
  deriving (Show, Eq, Ord)

instance Grammar Expr where
  data NT Expr
    = NTExpr
    | NTString
    | NTInt
    deriving (Show, Enum, Ord, Bounded, Eq)

  data T Expr
    = TString String
    | TInt Int
    deriving (Show, Eq, Ord)

  data ProdRule Expr
    = RVar
    | RConst
    | RPlus
    | RMult
    | RString
    | RInt
    deriving (Show, Enum, Ord, Bounded, Eq)

  -- encode = \case
  --   Var x -> Node RVar []
  --   Const x -> Node RConst []
  --   e1 `Plus` e2 -> Node RPlus [encode e1, encode e2]
  --   e1 `Mult` e2 -> Node RMult [encode e1, encode e2]

  -- decode (Node x ts) = case (x, ts) of
  --   (RVar, []) -> Just (Var "x")
  --   (RConst, []) -> Just (Const 0)
  --   (RPlus, [t1, t2]) -> Plus <$> decode t1 <*> decode t2
  --   (RMult, [t1, t2]) -> Mult <$> decode t1 <*> decode t2
  --   _ -> Nothing

  -- begin = Right NTExpr

  legalRule = \case
    Right NTExpr -> [RVar, RConst, RPlus, RMult]
    Right NTInt -> [RInt]
    Right NTString -> [RString]
    Left _ -> []

  -- argSymbol x = Left <$> case x of
  --     RVar        -> [NTString]
  --     RConst      -> [NTInt]
  --     RPlus       -> [NTExpr, NTExpr]
  --     RMult       -> [NTExpr, NTExpr]
  --     RString     -> []
  --     RInt        -> []

  safeApplyRule RString NTString = Just $ Left <$> [TString "x"]
  safeApplyRule RInt NTInt = Just $ Left <$> [TInt 42]
  safeApplyRule RVar NTExpr = Just $ [Right NTString]
  safeApplyRule RConst NTExpr = Just $ [Right NTInt]
  safeApplyRule RPlus NTExpr = Just $ Right <$> [NTExpr, NTExpr]
  safeApplyRule RMult NTExpr = Just $ Right <$> [NTExpr, NTExpr]
  safeApplyRule _ _ = Nothing

data Numeral
  = I
  | II
  | III
  | IV
  | V
  | VI
  | VII
  | Numeral `Of` Numeral
  deriving (Show, Eq, Ord, Generic)

instance HasTrie Numeral where
  newtype Numeral :->: b = NumeralTrie {unNumeralTrie :: Reg Numeral :->: b}
  trie = trieGeneric NumeralTrie
  untrie = untrieGeneric unNumeralTrie
  enumerate = enumerateGeneric unNumeralTrie

simplifyNumeral = \case
  x `Of` I -> x
  x `Of` y -> simplifyNumeral $ x `Of` simplifyNumeral y
  x -> x

-- >>> simplifyNumeral (III `Of` (I `Of` I))
-- III

isOf :: Numeral -> Bool
isOf (_ `Of` _) = True
isOf _ = False

vof :: Numeral -> Numeral
vof I = V
vof II = VI
vof III = VII
vof IV = I
vof V = II
vof VI = III
vof VII = IV

-- data Chord :: Numeral -> Numeral -> Type where
--   Chord :: Chord x y
--   D5 :: Chord (Vof x) y -> Chord x y -> Chord x y
--   AppD :: Chord V (x `Of` y) -> Chord I (x `Of` y) -> Chord x y
--   IV_V :: Chord IV y -> Chord V y -> Chord V y

ofKey :: Numeral -> Numeral -> T Chord
x `ofKey` y = TChord x y

data Chord

instance HasTrie (T Chord) where
  newtype (T Chord) :->: b = TChordTrie {unTChordTrie :: Reg (T Chord) :->: b}
  trie = trieGeneric TChordTrie
  untrie = untrieGeneric unTChordTrie
  enumerate = enumerateGeneric unTChordTrie

instance HasTrie (NT Chord) where
  newtype (NT Chord) :->: b = NTChordTrie {unNTChordTrie :: Reg (NT Chord) :->: b}
  trie = trieGeneric NTChordTrie
  untrie = untrieGeneric unNTChordTrie
  enumerate = enumerateGeneric unNTChordTrie

instance HasTrie (ProdRule Chord) where
  newtype (ProdRule Chord) :->: b = ProdRuleChordTrie {unProdRuleChordTrie :: Reg (ProdRule Chord) :->: b}
  trie = trieGeneric ProdRuleChordTrie
  untrie = untrieGeneric unProdRuleChordTrie
  enumerate = enumerateGeneric unProdRuleChordTrie

instance Grammar Chord where
  data T Chord
    = TChord Numeral Numeral
    deriving (Show, Ord, Eq, Generic)

  data NT Chord
    = NTChord Numeral Numeral
    deriving (Show, Ord, Eq, Generic)

  data ProdRule Chord
    = Chord
    | Prol
    | D5
    | AppD
    | IV_V
    deriving (Show, Enum, Ord, Bounded, Eq, Generic)

  nArg = \case
    Chord -> 0
    Prol -> 2
    D5 -> 2
    AppD -> 2
    IV_V -> 2

  legalRule (Right (NTChord V y)) = [Chord, Prol, D5, AppD, IV_V]
  legalRule (Right (NTChord x y)) = [Chord, Prol, D5, AppD]
  legalRule (Left _) = []

  safeApplyRule Chord (NTChord x y) = Just $ Left <$> [TChord x y]
  safeApplyRule Prol (NTChord x y) = Just $ Right <$> [NTChord x y, NTChord x y]
  safeApplyRule D5 (NTChord x y) = Just $ Right <$> [NTChord (vof x) y, NTChord x y]
  safeApplyRule AppD (NTChord x y) = Just $ Right <$> [NTChord V (x `Of` y), NTChord x y]
  safeApplyRule IV_V (NTChord x y)
    | x == V = Just $ Right <$> [NTChord IV y, NTChord V y]
    | otherwise = Nothing

  possibleMerges [Right (NTChord x y), Right (NTChord x' y')] =
    if
      | (x, y) == (x', y') -> [(NTChord x y, Prol)]
      | y == y', x == vof x' -> [(NTChord x' y', D5)]
      | y == y', (x, x') == (IV, V) -> [(NTChord x' y', IV_V)]
      | otherwise -> case y of
          a `Of` b ->
            if
              | (a, b) == (x', y'), x == V -> [(NTChord a b, AppD)]
              | otherwise -> []
          _ -> []
  possibleMerges [Left (TChord x y)] = [(NTChord x y, Chord)]
  possibleMerges _ = []

  terminate = Chord