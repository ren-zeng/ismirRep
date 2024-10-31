{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module ForwardChaining where

-- import Data.Set (Set, difference, fromList, insert, singleton, toList)

import qualified Combinatorics as Comb
import Control.Applicative
import Control.Monad (forM)
import Control.Monad.Extra
import Control.Monad.Trans.State
import Data.Graph (Graph)
import Data.List.Split (splitPlaces)
import Data.Map (Map, keys)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (insertAt)
import Data.Tree
import Debug.Trace
import GHC.List (List)
import GrammarInstances
import Preliminaries.Grammar
import Text.Pretty.Simple
import Text.Printf
import Prelude hiding (lookUp)

-- data WDeduction v w e = WDeduction
--   { items :: [v],
--     hyperEdges :: [e v w],
--     oPlus :: v -> w -> w -> w
--   }

data Rule a v w = Rule
  { -- split :: v -> Maybe (Set v),
    name :: a,
    merge :: List v -> Maybe v,
    combine :: [w] -> w,
    nPremises :: Int
  }

data HyperEdge a v w = HyperEdge
  { edgeLabel :: a,
    edgeTarget :: v,
    combFunc :: [w] -> w,
    edgeSources :: List v
  }

instance (Show v, Show a) => Show (HyperEdge a v w) where
  show e =
    printf
      "%s ← %s ⤙ %s"
      (show $ edgeTarget e)
      (show $ edgeLabel e)
      (show $ edgeSources e)

class RuleLike r where
  consequent :: r a v w -> List v -> Maybe v
  ruleName :: r a v w -> a

  -- premises :: e v w -> v -> Maybe (Set v)
  combination :: r a v w -> [w] -> w
  arity :: r a v w -> Int

instance RuleLike Rule where
  ruleName = name
  consequent = merge

  -- premises = split
  combination = combine
  arity = nPremises

class Chart f where
  out :: (Ord v, Show v, RuleLike r, Show a) => [r a v w] -> f a v w -> v -> [HyperEdge a v w]

class (Chart f) => ChartIn f where
  inEdges :: (Ord v) => f a v w -> v -> [HyperEdge a v w]

data HyperGraph a v w = HyperGraph
  { hyperEdges :: [HyperEdge a v w],
    vertexWeights :: Map v w
  }
  deriving (Show)

inHyperGraph :: (Ord v) => v -> HyperGraph a v w -> Bool
inHyperGraph v g = v `Map.member` vertexWeights g

describeHyperGraph :: HyperGraph a v w -> String
describeHyperGraph x =
  printf
    "has %s vertex and %s hyperedges"
    (show . length $ hyperEdges x)
    (show . length $ vertexWeights x)

allInserts :: a -> [a] -> [[a]]
allInserts a [] = [[a]]
allInserts a (x : xs) = (a : x : xs) : ((x :) <$> allInserts a xs)

-- >>> allInserts 2 [9,8,4]
-- [[2,9,8,4],[9,2,8,4],[9,8,2,4],[9,8,4,2]]

instance Chart HyperGraph where
  out rules chart v = do
    r <- rules

    known <- chooseN (arity r - 1) (keys (vertexWeights chart))
    premises <- allInserts v known
    let mConclusion = consequent r premises
    guard (isJust $ mConclusion)
    let Just conclusion = mConclusion
    -- traceM $
    --   printf
    --     "🟢  %s ← %s - %s ++ %s"
    --     (show conclusion)
    --     (show (ruleName r))
    --     (show [v])
    --     (show known)
    return $ HyperEdge (ruleName r) conclusion (combination r) premises

instance ChartIn HyperGraph where
  inEdges chart v = filter (\(HyperEdge _ v' _ _) -> v' == v) (hyperEdges chart)

chooseN = Comb.variate

-- >>> length$  chooseN 3 (fromList "abcdefg")
-- 35

class HyperGraphLike f where
  lookUpV :: (Ord v) => f a v w -> v -> Maybe w
  addE :: (Ord v, Show v, Show a) => (v -> w -> w -> w) -> HyperEdge a v w -> f a v w -> f a v w

instance HyperGraphLike HyperGraph where
  lookUpV = (Map.!?) . vertexWeights
  addE plus e@(HyperEdge _ v f us) x =
    trace ("✨adding " ++ show e) $
      x {hyperEdges = e : hyperEdges x, vertexWeights = Map.insert v wNew $ vertexWeights x}
    where
      w = f . mapMaybe (lookUpV x) $ us
      wNew = case lookUpV x v of
        Nothing -> w
        Just w' -> plus v w' w

class SetLike f where
  push :: a -> f a -> f a
  pop :: f a -> (a, f a)
  isEmpty :: f a -> Bool
  isIn :: (Eq a) => a -> f a -> Bool

instance SetLike [] where
  push = (:)
  pop [] = error "pop on empty list"
  pop (x : xs) = (x, xs)
  isEmpty = null
  isIn = elem

forwardChain' ::
  (Chart t, RuleLike r, HyperGraphLike t, SetLike f, Eq w, _) =>
  [r a v w] ->
  (v -> w -> w -> w) ->
  (t a v w, f v) -> -- (chart,agenda)
  (t a v w, f v)
forwardChain' rules plus (chart, agenda) =
  -- trace (printf "hello %s" $ show (chart, agenda)) $
  if isEmpty agenda
    then (chart, agenda)
    else go rules plus (chart, agenda)

go ::
  (_) =>
  [e a v w] ->
  (v -> w -> w -> w) ->
  (t a v w, f v) ->
  (t a v w, f v)
go rules plus (chart, agenda) = do
  let (u, a) = pop agenda
      (_c, _a) = foldr (addNewItem plus) (chart, a) (out rules chart u)
  forwardChain' rules plus (_c, _a)

recoverParseForest ::
  (Eq w, Chart t, _) =>
  t a v w ->
  v ->
  [Tree v]
recoverParseForest chart v = do
  if null $ inEdges chart v
    then return $ Node v []
    else do
      e <- inEdges chart v
      let us = edgeSources e
      -- traceM $ (show us) ++ "::: " ++ (show $ recoverParseForest chart <$> us)
      ts <- mapM (recoverParseForest chart) us
      return $ Node v ts

addNewItem plus e@(HyperEdge _ v f us) (c, a) =
  let c' = addE plus e c
   in if lookUpV c' v /= lookUpV c v && not (isIn v a)
        then (c', push v a)
        else (c', a)

forwardChain rules wAxioms plus =
  forwardChain'
    rules
    plus
    (wAxioms, keys $ vertexWeights wAxioms)

data family Item k a

-- data Curried a = Atom a | Binarized (a -> Curried a -> Maybe (Curried a))

-- partialAppRule :: ([a] -> Maybe a) -> a -> Curried a -> Maybe (Curried a)
-- partialAppRule f x = \case
--   Atom y -> do
--     y' <- f [x, y]
--     return $ Atom y'
--   Binarized g -> f

data CYK

data instance Item CYK a
  = IsWord (T a) Int Int
  | IsPhrase (NT a) Int Int

deriving instance Show (Item CYK Chord)

deriving instance Ord (Item CYK Chord)

deriving instance Eq (Item CYK Chord)

cykAxiom :: Rule () (Item CYK Chord) Double
cykAxiom =
  Rule
    ()
    ( \s -> case s of
        [IsWord (TChord x y) i j] ->
          if j == i + 1
            then Just $ IsPhrase (NTChord x y) i j
            else Nothing
        _ -> Nothing
    )
    (sum @_ @Double)
    1

traceGuard :: (Monad f) => String -> String -> (Bool -> f ()) -> (Bool -> f ())
traceGuard tString fString f = \case
  True -> do traceM tString; f True
  False -> do traceM fString; f False

cykInference :: Rule () (Item CYK Chord) Double
cykInference =
  Rule
    ()
    ( \l ->
        case l of
          [IsPhrase y i j, IsPhrase z j' k] -> do
            traceGuard ("🔹 " ++ show l) ("🔺 " ++ show l) guard $ j == j' && i < j && j' < k
            x <- listToMaybe . fmap fst $ possibleMerges [Right y, Right z]
            traceM ("🔸 " ++ show l)
            return (IsPhrase x i k)
          _ -> do
            traceM ("🟥 " ++ show l)
            Nothing
    )
    (sum @_ @Double)
    2

-- >>> possibleMerges [Right $ NTChord V I,Right $ NTChord I I]
-- [(NTChord I I,D5)]

r = length $ recoverParseForest (builtCykChart testChords) goal
  where
    goal = IsPhrase (NTChord I I) 0 (length testChords)

testChords =
  ( (`TChord` I)
      <$> (concat . replicate 40) [VI, II, V, I]
  )

builtCykChart :: [T Chord] -> HyperGraph () (Item CYK Chord) Double
builtCykChart xs =
  fst $
    forwardChain
      [cykAxiom, cykInference]
      (initializeChartCYK xs)
      (const (min))

initializeChartCYK :: (_) => [T Chord] -> HyperGraph () (Item CYK Chord) w
initializeChartCYK = initializeChart (fromTerminals $ \x n -> IsWord x n (n + 1))

initializeChart :: (_) => ([T a] -> [Item k a]) -> [T a] -> HyperGraph b (Item k a) w
initializeChart f xs =
  HyperGraph [] $
    Map.fromList $
      zip (f xs) [1, 1 ..]

fromTerminals :: (T a -> Int -> Item k a) -> [T a] -> [Item k a]
fromTerminals f = fromChords' 0
  where
    fromChords' n [] = []
    fromChords' n (x : xs) = f x n : fromChords' (n + 1) xs
