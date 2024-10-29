{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module TemplateForwardChaining where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.List (permutations)
import Data.Map (keys)
import qualified Data.Set as Set
import Debug.Trace
import ForwardChaining
import GrammarInstances
import Meta
import Preliminaries.Grammar (Grammar (nArg), rules)
import TemplateGrammar

data TG

data Span = ZeroSpan | Span Int Int deriving (Show, Eq, Ord)

spanSum :: [Span] -> Maybe Span
spanSum = foldM (|+|) ZeroSpan

(|+|) :: Span -> Span -> Maybe Span
ZeroSpan |+| y = Just y
x |+| ZeroSpan = Just x
x@(Span x1 _) |+| y@(Span _ y2) =
  if x >|< y
    then Just $ Span x1 y2
    else Nothing

(>|<) :: Span -> Span -> Bool
(Span _ y1) >|< (Span x2 _) = y1 == x2

data instance Item TG Chord
  = IsW (T Chord) [Span]
  | IsP (NT Chord) [Span] (HoleTree (ProdRule Chord))
  deriving (Eq, Ord, Show)

spansOf :: Item TG Chord -> [Span]
spansOf (IsW _ x) = x
spansOf (IsP _ x _) = x

headOf :: Item TG Chord -> Maybe (NT Chord)
headOf (IsP x ss t) = Just x
headOf _ = Nothing

holeTreeOf :: Item TG Chord -> HoleTree (ProdRule Chord)
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
-- inferenceTemplate2 :: Rule Meta (Item TG Chord) Int
-- inferenceTemplate2 = Rule (\s -> asum (g <$> permutations (toList s))) sum 2
--   where
--     g = \case
--       [IsP x [sL, sR] tX, IsP y ss tY] -> case ss of
--         [s1] -> do
--           r <- spanSum [sL, s1, sR]
--           guard $ argTypes x tX == Just [y]
--           guard $ s1 /= ZeroSpan
--           return $ IsP x [r] (WithRep tX [New] [tY])
--         [s1, s2] -> do
--           rL <- sL |+| s1
--           rR <- s2 |+| sR
--           guard $ argTypes x tX == Just [y]
--           asum
--             [ do
--                 guard (tX == tY)
--                 return $ IsP x [rL, rR] (WithRep tX [Star] []),
--               return $ IsP x [rL, rR] (WithRep tX [New] [tY])
--             ]
--         [s1, s2, s3] -> undefined
--         _ -> Nothing
--       _ -> Nothing

interleave :: [a] -> [a] -> [a]
interleave = undefined

safeUnpack :: Int -> [a] -> Maybe [a]
safeUnpack n xs = do
  guard $ length xs == n
  return xs

inferenceTemplate :: [Int] -> Meta -> Rule (Maybe Meta) (Item TG Chord) Int
inferenceTemplate ns mt = Rule (Just mt) f sum k
  where
    k = length ns + 1
    f s = asum $ g <$> permutations (toList s)
    g l = do
      guard (length l == 3)
      (IsP x topSpans tX) : bs <- safeUnpack k l
      let allBotSpans = spansOf <$> bs
      guard $ sum (length <$> allBotSpans) <= 2
      guard (all notEmptyZeroHole allBotSpans)

      -- traceM $ "topSpans" ++ show topSpans
      -- traceM $ "allBotSpans" ++ show allBotSpans
      -- traceM "\n"
      guard (length topSpans == length bs + 1)
      combinedSpans <- substituteHoles topSpans allBotSpans
      -- traceM ("combinedSpans: " ++ show combinedSpans)
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
  HoleTree (ProdRule Chord) ->
  [HoleTree (ProdRule Chord)] ->
  Maybe (HoleTree (ProdRule Chord))
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

-- >>> substituteHoles [ZeroSpan,ZeroSpan,ZeroSpan] [[ZeroSpan,ZeroSpan],[ZeroSpan,ZeroSpan]]
-- Just [ZeroSpan,ZeroSpan,ZeroSpan]

-- inferenceTemplate3 :: Rule Meta (Item TG Chord) Int
-- inferenceTemplate3 = Rule f sum 3
--   where
--     f s = case toList s of
--       [v1, v2, v3] ->
--         asum $
--           ( \l -> case l of
--               [(IsP x [sL, sM, sR] tX), (IsP y [s1] tY), (IsP z [s2] tZ)] -> do
--                 -- traceM ("???" ++ show s)
--                 sp <- foldM (|+|) ZeroSpan [sL, s1, sM, s2, sR]
--                 guard $ s1 /= ZeroSpan && s2 /= ZeroSpan
--                 guard $ argTypes x tX == Just [y, z]
--                 -- traceM ("🔸" ++ show s)
--                 return $ IsP x [sp] (WithRep tX [New, New] [tY, tZ])
--               _ -> Nothing
--           )
--             <$> permutations [v1, v2, v3]
--       _ -> Nothing

-- >>> foldM (|+|) ZeroSpan  [Span 1 3, Span 3 6, Span 0 1]
-- Nothing

initializeChartTemplate :: [T Chord] -> HyperGraph (Maybe Meta) (Item TG Chord) Int
initializeChartTemplate =
  initializeChart
    ((++ [IsP nt (replicate (nArg r + 1) ZeroSpan) (HoleTree r (replicate (nArg r) Hole)) | r <- rules, nt <- [NTChord I I, NTChord II I, NTChord IV I, NTChord V I]]) . fromTerminals (\x n -> IsW x [Span n (n + 1)]))

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

a :: HyperGraph (Maybe Meta) (Item TG Chord) Int
a =
  fst $
    forwardChain
      (axiomTemplate : [inferenceTemplate ns mt | (ns, mt) <- allHoleCases])
      (initializeChartTemplate $ (`TChord` I) <$> [I, VI, II, V, VI, II, V, I, I, VI, II, V, VI, II, V, I])
      (const min)

-- tryMerging =
--   merge
--     (inferenceTemplate [0, 0] [New, RepLoc 1])
--     ( Set.fromList
--         [IsP nt (replicate (nArg r + 1) ZeroSpan) (HoleTree r []) | r <- rules, nt <- [NTChord I I]]
--     )

-- >>> tryMerging
-- Just (IsP (NTChord I I) [Span 0 5] (WithRep (Template Prol) [New,RepLoc 1] [Template Chord]))

-- >>>
