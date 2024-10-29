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

import Control.Applicative
import Control.Monad (forM)
import Control.Monad.Extra
import Control.Monad.Trans.State
import Data.Graph (Graph)
import Data.List (permutations)
import Data.Map (Map, keys)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set, difference, fromList, insert, singleton, toList)
import Data.Tree
import Debug.Trace
import GrammarInstances
import Preliminaries.Grammar
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
    merge :: Set v -> Maybe v,
    combine :: [w] -> w,
    nPremises :: Int
  }

data HyperEdge a v w = HyperEdge a v ([w] -> w) (Set v)

instance (Show v, Show a) => Show (HyperEdge a v w) where
  show (HyperEdge x v _ us) = printf "%s <- %s -< %s" (show v) (show x) (show us)

class RuleLike r where
  consequent :: r a v w -> Set v -> Maybe v
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

describeHyperGraph :: HyperGraph a v w -> String
describeHyperGraph x =
  printf
    "has %s vertex and %s hyperedges"
    (show . length $ hyperEdges x)
    (show . length $ vertexWeights x)

instance Chart HyperGraph where
  out rules chart v = do
    r <- rules
    -- if arity r == 1
    --   then do
    --     guard (isJust $ consequent r (fromList [v]))
    --     let Just conclusion = consequent r (fromList [v])
    --     traceM $
    --       printf
    --         "🟢  %s ← %s - %s"
    --         (show conclusion)
    --         (show (ruleName r))
    --         (show [v])
    --     return $ HyperEdge (ruleName r) conclusion (combination r) (fromList [v])
    --   else do
    known <- chooseN (arity r - 1) (fromList $ keys (vertexWeights chart))
    -- traceM $ "known:" ++ show known
    let mConclusion = consequent r (insert v known)
    guard (isJust $ mConclusion)
    let Just conclusion = mConclusion
    traceM $
      printf
        "🟢  %s ← %s - %s ++ %s"
        (show conclusion)
        (show (ruleName r))
        (show [v])
        (show known)
    return $ HyperEdge (ruleName r) conclusion (combination r) (insert v known)

instance ChartIn HyperGraph where
  inEdges chart v = filter (\(HyperEdge _ v' _ _) -> v' == v) (hyperEdges chart)

chooseN :: (Ord a) => Int -> Set a -> [Set a]
chooseN 0 _ = [mempty]
chooseN 1 xs = singleton <$> toList xs
chooseN n xs = toList . fromList $ do
  xs' <- chooseN (n - 1) xs
  x <- chooseN 1 $ difference xs xs'
  return $ x <> xs'

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
      w = f . mapMaybe (lookUpV x) . toList $ us
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
  HyperEdge _ _ _ us <- inEdges chart v
  u <- toList us
  return $ Node v (recoverParseForest chart u)

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
    ( \s -> case toList s of
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
    ( \s ->
        asum $
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
            <$> permutations (toList s)
            -- _ -> do
            --   -- traceM ("🔺" ++ show s)
            --   Nothing
    )
    (sum @_ @Double)
    2

-- >>> possibleMerges [Right $ NTChord V I,Right $ NTChord I I]
-- [(NTChord I I,D5)]

r = length $ recoverParseForest builtCykChart goal
  where
    goal = IsPhrase (NTChord I I) 0 5

builtCykChart :: HyperGraph () (Item CYK Chord) Double
builtCykChart =
  fst $
    forwardChain
      [cykAxiom, cykInference]
      cykChart
      (const (min))

cykChart :: HyperGraph () (Item CYK Chord) Double
cykChart =
  initializeChartCYK
    ( (`TChord` I)
        <$> (concat . replicate 1) [I, IV, II, V, I]
    )

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
