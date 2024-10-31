{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module TemplateForwardChaining where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Map (keys)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace
import ForwardChaining
import GrammarInstances
import Meta
import Preliminaries.Grammar (Grammar (nArg), rules)
import TemplateGrammar
import Text.Pretty.Simple

-- | A tag for a data family instance
data TG

-- | A representation of interval on Int
data Span = ZeroSpan | Span Int Int deriving (Show, Eq, Ord)

spanSum :: [Span] -> Maybe Span
spanSum = foldM (|+|) ZeroSpan

(|+|) :: Span -> Span -> Maybe Span
ZeroSpan |+| y = Just y
x |+| ZeroSpan = Just x
(Span x1 x2) |+| (Span y1 y2) = do
  guard $ x2 == y1
  return $ Span x1 y2

-- | The set of proposition when parsing template grammar
data instance Item TG a
  = IsW (T a) [Span]
  | IsP (NT a) [Span] (HoleTree (ProdRule a))

-- deriving (Eq, Ord, Show)

deriving instance (Grammar a) => Eq (Item TG a)

deriving instance (Grammar a, Ord (T a), Ord (NT a), Ord (ProdRule a)) => Ord (Item TG a)

deriving instance (Grammar a) => Show (Item TG a)

spansOf :: Item TG a -> [Span]
spansOf (IsW _ x) = x
spansOf (IsP _ x _) = x

headOf :: Item TG a -> Maybe (NT a)
headOf (IsP x ss t) = Just x
headOf _ = Nothing

holeTreeOf :: Item TG a -> HoleTree (ProdRule a)
holeTreeOf (IsP _ _ t) = t

axiomTemplate :: Rule (Maybe Meta) (Item TG Chord) Int
axiomTemplate =
  Rule
    Nothing
    ( \s -> case toList s of
        [IsW (TChord x y) [Span i j]] ->
          if j == i + 1
            then Just $ IsP (NTChord x y) [Span i j] (HoleTree Chord [])
            else Nothing
        _ -> Nothing
    )
    sum
    1

{-
case analysis on the number of (premises)

2 = (1 [0]) | (1 [1]) | (1 [2])
3 = (2 [1,1]) | (2 [0,1]) | (2 [1,0]) | (2 [0,0])

-}

safeUnpack :: Int -> [a] -> Maybe [a]
safeUnpack n xs = do
  guard $ length xs == n
  return xs

inferenceTemplate :: (Grammar a) => [Int] -> Meta -> Rule (Maybe Meta) (Item TG a) Int
inferenceTemplate ns mt = Rule (Just mt) f sum k
  where
    k = length ns + 1
    f l = do
      (IsP x topSpans tX) : bs <- safeUnpack k l
      let allBotSpans = spansOf <$> bs
      guard $ sum (length <$> allBotSpans) <= 2
      guard $ all notEmptyZeroHole allBotSpans
      guard $ length topSpans == length bs + 1
      combinedSpans <- substituteHoles topSpans allBotSpans
      guard (combinedSpans /= topSpans)
      ys <- mapM headOf bs
      guard (argTypes x tX == Just ys)
      let (m, freeBs) = inferMeta tX (holeTreeOf <$> bs)
      guard $ mt == m
      holeTree <- assembleHoleTree tX $ holeTreeOf <$> bs
      return $ IsP x combinedSpans holeTree

noHole :: HoleTree a -> Bool
noHole Hole = False
noHole (HoleTree _ ts) = all noHole ts

assembleHoleTree ::
  HoleTree (ProdRule a) ->
  [HoleTree (ProdRule a)] ->
  Maybe (HoleTree (ProdRule a))
assembleHoleTree t [] = Just t
assembleHoleTree Hole [b] = Just b
assembleHoleTree (HoleTree x (t : ts)) (b : bs) =
  if noHole t
    then do
      ts' <- mapM (`assembleHoleTree` (b : bs)) ts
      return $ HoleTree x (t : ts')
    else do
      t' <- assembleHoleTree t [b]
      ts' <- mapM (`assembleHoleTree` bs) ts
      return $ HoleTree x (t' : ts')
assembleHoleTree _ _ = Nothing

notEmptyZeroHole :: [Span] -> Bool
notEmptyZeroHole [x] = x /= ZeroSpan
notEmptyZeroHole _ = True

{-
(sL,sR) , [s1,s2,s3] |-> [sL + s1, s2, s3 + sR]
-}
substituteHole :: (Span, Span) -> [Span] -> Maybe [Span]
substituteHole (sL, sR) = \case
  [s] -> sequence [spanSum [sL, s, sR]]
  ss -> do
    front <- sL |+| head ss
    back <- last ss |+| sR
    return $ [front] ++ init (tail ss) ++ [back]

-- >>> substituteHole (ZeroSpan,ZeroSpan) [Span 0 1, Span 3 5,Span 8 11]
-- Just [Span 0 1,Span 3 5,Span 8 11]

{-
[ZeroSpan,ZeroSpan] [[Span 0 1, Span 3 5]]
ss = [Span 0 1,Span 3 5]
ss' = substituteHoles [Span 3 5] []
-}
substituteHoles :: [Span] -> [[Span]] -> Maybe [Span]
substituteHoles [x] [] = Just [x]
substituteHoles [sL, sR] [ss] = substituteHole (sL, sR) ss
substituteHoles [sL, sM, sR] [ss1, ss2] = do
  ss' <- substituteHole (sL, sM) ss1
  case ss' of
    [_s] -> substituteHole (_s, sR) ss2
    _ss -> do
      _ss' <- substituteHole (last _ss, sR) ss2
      return $ init _ss ++ _ss'
-- substituteHoles (sL : sR : sTail) (ss1 : sss) = do
--   ss <- substituteHole (sL, sR) ss1
--   case ss of
--     [s] -> (s :) <$> substituteHoles sTail sss
--     _ -> do
--       let initS = init ss
--       let lastS = last ss
--       ss' <- substituteHoles (lastS : sTail) sss
--       return $ initS ++ ss'
substituteHoles _ _ = Nothing

-- >>> substituteHole (ZeroSpan,ZeroSpan) [Span 0 1]
-- Just [Span 0 1]

-- >>> substituteHole (Span 0 1,ZeroSpan) [Span 3 5]
-- Nothing

-- >>> substituteHoles [ZeroSpan,ZeroSpan,ZeroSpan] [[Span 0 1],[Span 1 5]]
-- Just [Span 0 5]

initializeChartTemplate :: [T Chord] -> HyperGraph (Maybe Meta) (Item TG Chord) Int
initializeChartTemplate = initializeChart (\xs -> prodRuleAxioms ++ termialAxioms xs)
  where
    termialAxioms = fromTerminals (\x n -> IsW x [Span n (n + 1)])
    prodRuleAxioms = do
      r <- rules
      nt <- [NTChord I I, NTChord II I, NTChord IV I, NTChord V I]
      return $ IsP nt (replicate (nArg r + 1) ZeroSpan) (HoleTree r (replicate (nArg r) Hole))

allHoleCases :: [([Int], Meta)]
allHoleCases =
  [ ([1], [New]),
    ([1], [Star]),
    ([2], [New]),
    ([0, 0], [New, New]),
    ([0, 0], [New, RepLoc 1]),
    ([0, 1], [New, New]),
    ([1, 1], [New, New]),
    ([1, 1], [New, RepLoc 1]),
    ([1, 0], [New, New]),
    ([2, 0], [New, New]),
    ([2, 0], [Star, New]),
    ([0, 2], [New, New]),
    ([2, 0], [New, New])
  ]

inferChordTemplate :: [T Chord] -> HyperGraph (Maybe Meta) (Item TG Chord) Int
inferChordTemplate xs =
  fst $
    forwardChain
      (axiomTemplate : [inferenceTemplate ns mt | (ns, mt) <- allHoleCases])
      (initializeChartTemplate xs)
      (const min)

sumMap f = foldr (\a -> (+ f a)) 0

-- findMinimal ::
--   Item TG Chord ->
--   HyperGraph (Maybe Meta) (Item TG Chord) Int ->
--   [Template (ProdRule Chord)]
-- findMinimal goal hyper = do
--   let weight = (vertexWeights hyper Map.!)
--   guard $ goal `inHyperGraph` hyper
--   e <- inEdges hyper goal
--   let vs = edgeSources e
--   guard $ sumMap weight vs == weight goal
--   case edgeLabel e of
--     Nothing -> return $ Template Chord
--     Just m -> do
--       let tX = head vs
--       return $ WithRep tX m tYs

a :: HyperGraph (Maybe Meta) (Item TG Chord) Int
a = inferChordTemplate $ (`TChord` I) <$> [V, I]
