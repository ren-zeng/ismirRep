{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module ParsingTemplateGrammar where

import Control.Applicative (Alternative, asum)
import Control.Arrow
import Control.Monad (guard, zipWithM)
import Data.Either (isRight, lefts, rights)
import Data.Function
import Data.Functor.Foldable (hylo)
import Data.List hiding (product, sum)
import Data.List.Extra (notNull)
import Data.List.Split
import Data.Maybe (catMaybes)
import Data.MemoTrie (memoFix)
import Data.Semiring hiding ((-))
import Data.Tree
import GHC.Base hiding (One, Symbol, foldr)
import Grammar hiding (Plus)
import Meta
import SemiringParsing
import TemplateGrammar
import Prelude hiding (product, sequence, sum, (+))

data Item x e = Item x e deriving (Eq, Show)

data ProdSum a = ProdSum a | And [ProdSum a] | Or [ProdSum a]

type TemplateItem a = Item (NT a) [[T a]]

splitFrontier :: [Either a b] -> [[a]]
splitFrontier = fmap lefts . splitWhen isRight

-- >>> splitFrontier [Left $ TChord V I,Left $ TChord I I, Right $ NTChord V I, Left $ TChord I I,Right $ NTChord I I]
-- [[TChord V I,TChord I I],[TChord I I],[]]

evidence :: (Grammar a) => NT a -> Template (ProdRule a) -> [[T a]]
evidence x = splitFrontier . applyTemplate x

-- >>> evidence (NTChord I I) ( Comp 1 (Template RD5) (Comp 1 (Template RD5) (Template RChord)))
-- [[TChord II I],[],[]]

explainFrontier' :: (Grammar a) => (NT a -> [[T a]] -> [Template (ProdRule a)]) -> NT a -> [[T a]] -> [Template (ProdRule a)]
explainFrontier' f x ls = case ls of
  [[], [], []] -> baseParse x ls
  _ ->
    if notNull (baseParse x ls)
      then baseParse x ls
      else case ls of
        [l] -> zeroHoleParse f x l
        [l1, l2] -> oneHoleParse f x l1 l2
        [l1, l2, l3] -> twoHoleParse f x l1 l2 l3
        _ -> []

explainFrontier :: (Grammar a) => NT a -> [[T a]] -> [Template (ProdRule a)]
explainFrontier = fix explainFrontier'

-- >>> length $ explainFrontier (NTChord I I) [[TChord I I,TChord I I,TChord I I]]
-- 46

testTemplateParse :: (Grammar a) => NT a -> [[T a]] -> Bool
testTemplateParse x e =
  all
    (\t -> lefts (applyTemplate x t) == concat e)
    (explainFrontier x e)

-- >>> testTemplateParse (NTChord I I) [[TChord II I, TChord V I,TChord V I,TChord I I,TChord I I]]
-- ProgressCancelledException

baseParse ::
  (m ~ [], Monad m, Alternative m, Grammar a) =>
  NT a ->
  [[T a]] ->
  m (Template (ProdRule a))
baseParse x ls = do
  r <- legalRule (Right x)
  let t = Template r
  guard (evidence x t == ls)
  return t

-- >>> evidence (NTChord I I)  (Template RProl)
-- [[],[],[]]

testGuard :: (NT a -> [[T a]] -> [Template (ProdRule a)]) -> NT a -> [[T a]] -> [Template (ProdRule a)]
testGuard f x l = do
  guard (any notNull l)
  f x l

-- >>> testGuard
-- []

zeroHoleParse ::
  (m ~ [], Grammar a, Alternative m) =>
  (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
  NT a ->
  [T a] ->
  m (Template (ProdRule a))
zeroHoleParse f x l =
  asum
    [ do
        [l1, l2, l3] <- splitsN 3 l
        guard (l2 /= l)
        guard (notNull l2)
        α <- f x [l1, l3]
        -- guard (isLegal x α)
        let [y] = argTypes x α
        β <- f y [l2]
        return (WithRep α [New] [β]),
      do
        [l1, l2, l3, l4, l5] <- splitsN 5 l
        guard (l `notElem` [l2, l4])
        guard (notNull l2)
        guard (notNull l4)
        α <- f x [l1, l3, l5]
        -- guard (isLegal x α)
        let [y, z] = argTypes x α
        β <- f y [l2]
        γ <- f z [l4]
        return $
          if β == γ
            then WithRep α [New, RepLoc 1] [β]
            else WithRep α [New, New] [β, γ]
    ]

oneHoleParse ::
  (m ~ [], Grammar a) =>
  (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
  NT a ->
  [T a] ->
  [T a] ->
  m (Template (ProdRule a))
oneHoleParse f x l_L l_R =
  asum
    [ do
        [l1, l2] <- splitsN 2 l_L
        [l3, l4] <- splitsN 2 l_R
        guard ([l1, l4] /= [l_L, l_R])
        guard ([l2, l3] /= [l_L, l_R])
        α <- f x [l1, l4]
        -- guard (isLegal x α)
        let [y] = argTypes x α
        β <- f y [l2, l3]
        return $
          if α == β
            then WithRep α [Star] []
            else WithRep α [New] [β],
      do
        [l2, l3, l4] <- splitsN 3 l_R
        let l1 = l_L
        guard (notNull l3)
        α <- f x [l1, l2, l4]
        -- guard (isLegal x α)
        let [_, z] = argTypes x α
        β <- f z [l3]
        return $ Comp 2 α β,
      do
        [l1, l2, l3] <- splitsN 3 l_L
        let l4 = l_R
        guard (notNull l2)
        α <- f x [l1, l3, l4]
        -- guard (isLegal x α)
        let [y, _] = argTypes x α
        β <- f y [l2]
        return $ Comp 1 α β
    ]

twoHoleParse ::
  (Grammar a) =>
  (NT a -> [[T a]] -> [Template (ProdRule a)]) ->
  NT a ->
  [T a] ->
  [T a] ->
  [T a] ->
  [Template (ProdRule a)]
twoHoleParse f x l_L l_M l_R =
  asum
    [ do
        [l1, l2] <- splitsN 2 l_L
        let l3 = l_M
        [l4, l5, l6, l7] <- splitsN 4 l_R
        guard ([l_L, l_M, l_R] `notElem` [[l1, l5, l7], [l2, l3, l4]])
        α <- f x [l1, l5, l7]
        -- guard (isLegal x α)
        guard (notNull l6)
        let [y, z] = argTypes x α
        β1 <- f y [l2, l3, l4]
        β <- f z [l6]
        return $
          if α == β1
            then WithRep α [Star, New] [β]
            else WithRep α [New, New] [β1, β],
      do
        [[l1, l2, l3, l4], [l5], [l6, l7]] <- zipWithM splitsN [4, 1, 2] [l_L, l_M, l_R]
        guard ([l_L, l_M, l_R] `notElem` [[l1, l3, l7], [l4, l5, l6]])
        α <- f x [l1, l3, l7]
        -- guard (isLegal x α)
        guard (notNull l2)
        let [y, z] = argTypes x α
        β <- f y [l2]
        β1 <- f z [l4, l5, l6]
        return $
          if α == β1
            then WithRep α [New, Star] [β]
            else WithRep α [New, New] [β, β1],
      do
        [[l1, l2], [l3, l4], [l5]] <- zipWithM splitsN [2, 2, 1] [l_L, l_M, l_R]
        guard ([l_L, l_M, l_R] /= [l1, l4, l5])
        α <- f x [l1, l4, l5]
        -- guard (isLegal x α)
        let [y, _] = argTypes x α
        β <- f y [l2, l3]
        return $ Comp 1 α β,
      do
        [[l1], [l2, l3], [l4, l5]] <- zipWithM splitsN [1, 2, 2] [l_L, l_M, l_R]
        guard ([l_L, l_M, l_R] /= [l1, l2, l5])
        α <- f x [l1, l2, l5]
        guard (isLegal x α)
        let [_, z] = argTypes x α
        β <- f z [l3, l4]
        return $ Comp 2 α β,
      do
        [[l1, l2], [l3], [l4, l5]] <- zipWithM splitsN [2, 1, 2] [l_L, l_M, l_R]
        α <- f x [l1, l5]
        -- guard (isLegal x α)
        let [y] = argTypes x α
        β <- f y [l2, l3, l4]
        return $ WithRep α [New] [β],
      do
        [[l1, l2], [l3, l4, l5], [l6, l7]] <- zipWithM splitsN [2, 3, 2] [l_L, l_M, l_R]
        guard ([l_L, l_M, l_R] /= [l1, l4, l7])
        α <- f x [l1, l4, l7]
        -- guard (isLegal x α)
        let [y, z] = argTypes x α
        β <- f y [l2, l3]
        γ <- f z [l5, l6]
        return $
          if β == γ
            then WithRep α [New, RepLoc 1] [β]
            else WithRep α [New, New] [β, γ]
    ]

-- zeroHoleParse :: (Semiring b) => ([[a]] -> b) -> ([b] -> [b]) -> [a] -> b
-- zeroHoleParse f merges l =
--   (foldMapT . foldMapT . merges $ f)
--     [ do
--         [l1, l2, l3] <- splitsN 3 l
--         return [[l1, l3], [l2]],
--       do
--         [l1, l2, l3, l4, l5] <- splitsN 5 l
--         return [[l1, l3, l5], [l2], [l4]]
--     ]

-- oneHoleParse :: (Semiring b) => ([[a]] -> b) -> [a] -> [a] -> b
-- oneHoleParse f l_L l_R =
--   (foldMapT . foldMapT . foldMapP $ f)
--     [ do
--         [l1, l2] <- splitsN 2 l_L
--         [l3, l4] <- splitsN 2 l_R
--         return [[l1, l4], [l2, l3]],
--       do
--         let l1 = l_L
--         [l2, l3, l4] <- splitsN 3 l_R
--         return [[l1, l2, l4], [l3]],
--       do
--         let l4 = l_L
--         [l1, l2, l3] <- splitsN 3 l_L
--         return [[l1, l3, l4], [l2]]
--     ]

-- twoHoleParse :: (Semiring b) => ([[a]] -> b) -> [a] -> [a] -> [a] -> b
-- twoHoleParse f l_L l_M l_R =
--   (foldMapT . foldMapT . foldMapP $ f)
--     [ do
--         [l1, l2] <- splitsN 2 l_L
--         let l3 = l_M
--         [l4, l5, l6, l7] <- splitsN 4 l_R
--         return [[l1, l5, l7], [l2, l3, l4], [l6]]
--     ]

-- elementaryMerge :: (Grammar a) => NT a -> [Template (ProdRule a)] -> [[T a]] -> FreeSemiring (TemplateItem a)
-- elementaryMerge x elementary l = sum $ do
--   t <- elementary
--   guard (evidence x t == l)
--   return $ Val (Item x t l)

-- elementarySolve :: (Grammar a) => [Template (ProdRule a)] -> TemplateItem a -> FreeSemiring (TemplateItem a)
-- elementarySolve elementary (Item x l)
--   | t `elem` elementary && evidence x t == l = Val (Item x t l)
--   | otherwise = Zero

-- possibleCauses :: (Grammar a) => (NT a -> [Template (ProdRule a)]) -> TemplateItem a -> FreeSemiring (TemplateItem a)
-- possibleCauses elementary x@(Item nt e) =
--   (sum . fmap ($ x))
--     [ elementarySolve (elementary nt),
--       ind_0holeβ1,
--       ind_0holeβ1γ1,
--       ind_0holeβ1β1
--     ]

-- >>> possibleCauses elementary

-- solveItem :: (Semiring b, Grammar a) => [NT a -> Template (ProdRule a)] -> TemplateItem a -> b
-- solveItem elementary = hylo evalSemiring (possibleCauses elementary)

-- testSolve =
--   simpl $
--     possibleCauses (Template <$> rules) $
--       Item
--         (NTChord I I)
--         (WithRep (Template RProl) [New, RepLoc 1] [Template RChord])
--         [[TChord I I, TChord I I]]

-- >>> testSolve
-- Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[TChord I I,TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I,TChord I I]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[TChord I I],[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[TChord I I],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[TChord I I,TChord I I],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[TChord I I],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I,TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[TChord I I],[],[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[TChord I I],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[TChord I I],[TChord I I],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[TChord I I],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[TChord I I]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) (Plus (Times (Val (Item (NTChord I I) (Template RProl) [[TChord I I,TChord I I],[],[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) (Times (Val (Item (NTChord I I) (Template RChord) [[]])) One))) Zero))))))))))))))

-- | All possible ways to split a list into n part (n>0).
splitsN :: Int -> [a] -> [[[a]]]
splitsN n l
  | n <= 0 = error "the number of chunks should be positive for splitsN "
  | n == 1 = [[l]]
  | n == 2 = zipWith (\a b -> [a, b]) (inits l) (tails l)
  | otherwise = do
      [l1, l2] <- splitsN 2 l
      ls <- splitsN (n - 1) l2
      return (l1 : ls)

-- >>>  splitsN 3 [1,2,3,4]
-- [[[],[],[1,2,3,4]],[[],[1],[2,3,4]],[[],[1,2],[3,4]],[[],[1,2,3],[4]],[[],[1,2,3,4],[]],[[1],[],[2,3,4]],[[1],[2],[3,4]],[[1],[2,3],[4]],[[1],[2,3,4],[]],[[1,2],[],[3,4]],[[1,2],[3],[4]],[[1,2],[3,4],[]],[[1,2,3],[],[4]],[[1,2,3],[4],[]],[[1,2,3,4],[],[]]]

-- base_0hole :: (Grammar a) => TemplateItem a -> FreeSemiring (TemplateItem a)
-- base_0hole = error "base_0hole not implemented"

-- ind_0holeβ1 :: (Grammar a) => TemplateItem a -> FreeSemiring (TemplateItem a)
-- ind_0holeβ1 (Item x [l]) = sum $ do
--   [l1, l2, l3] <- splitsN 3 l
--   let [y] = argTypes x α
--   return $ product (Val <$> [Item x [l1, l3], Item y [l2]])
-- ind_0holeβ1 _ = zero

-- ind_0holeβ1γ1 :: (Grammar a) => TemplateItem a -> FreeSemiring (TemplateItem a)
-- ind_0holeβ1γ1 = \case
--   Item x [l] -> sum $ do
--     [l1, l2, l3, l4, l5] <- splitsN 5 l
--     let [y, z] = argTypes x α
--     return $ (product . fmap Val) [Item x  [l1, l3, l5], Item  β [l2], Item z  [l4]]
--   _ -> zero

-- ind_0holeβ1β1 :: (Grammar a) => TemplateItem a -> FreeSemiring (TemplateItem a)
-- ind_0holeβ1β1 = \case
--   Item x [l] -> sum $ do
--     [l1, l2, l3, l4, l5] <- splitsN 5 l
--     let [y, z] = argTypes x α
--     return $ (product . fmap Val) [Item x [l1, l3, l5], Item y  [l2], Item z [l4]]
--   _ -> zero
