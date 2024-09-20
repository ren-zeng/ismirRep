{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TemplateGrammar where

import Control.Applicative
import Control.Monad
import Control.Monad.Bayes.Class (Log, MonadDistribution (uniformD), MonadFactor, condition, score)
import Control.Monad.Bayes.Sampler.Strict
import Data.Either (isLeft, isRight, lefts, rights)
import Data.Fix (hoistFix)
import Data.Functor.Base hiding (head, tail)
import Data.Functor.Foldable
import Data.Functor.Foldable (Recursive (cata), hoist)
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.List.Extra (replace)
import Data.Semiring hiding ((-))
import Data.Tree
import Grammar
import Meta
import PCFG (surface)
import TreeUtils
import Prelude hiding (sum, (+))

data Template a
  = Template a
  | Comp Int (Template a) (Template a)
  | WithRep (Template a) Meta [Template a]
  deriving (Eq, Show, Functor)

makeBaseFunctor ''Template

instance Applicative Template where
  pure = Template
  tf <*> tx = undefined

freeArgs :: Meta -> [a] -> [a]
freeArgs = simplifyByMeta

class Arity a where
  arity :: a -> Int

instance (Grammar a) => Arity (ProdRule a) where
  arity = nArg

instance (Arity a) => Arity (Template a) where
  arity (Template x) = arity x
  arity (Comp _ x y) = arity x + arity y - 1
  arity (WithRep a m as) = sum $ arity <$> useMeta m a as

class ArgTypes x a b where
  argTypes :: x -> a -> [b]

instance (Grammar a) => ArgTypes (NT a) (ProdRule a) (Symbol a) where
  argTypes x p = applyRule p x

instance forall a. (Grammar a) => ArgTypes (NT a) (Template (ProdRule a)) (NT a) where
  argTypes x (Template r) = rights $ argTypes @(NT a) @(ProdRule a) @(Symbol a) x r
  argTypes x (Comp i α β) = take (i - 1) (argTypes x α) ++ argTypes y β ++ drop i (argTypes x α)
    where
      y = argTypes @(NT a) @(Template (ProdRule a)) @(NT a) x α !! (i - 1)
  argTypes x (WithRep α m βs) = concat $ zipWith (argTypes @(NT a)) (argTypes x α) (useMeta m α βs)

-- >>> useMeta [Star,New] (Template RD5) [Template RProl]
-- [Template RD5,Template RProl]

nRule :: Template (ProdRule a) -> Int
nRule = cata $ \case
  TemplateF _ -> 1
  CompF _ n1 n2 -> n1 + n2
  WithRepF n1 _ ns -> n1 + sum ns

-- >>> nRule (WithRep (Template RProl) [New,RepLoc 1] [Template RChord])
-- 2

expandNthThat :: Int -> (a -> Bool) -> (a -> [a]) -> [a] -> [a]
expandNthThat n sat f [] = []
expandNthThat n sat f (x : xs) =
  if sat x
    then
      if n == 0
        then f x ++ xs
        else x : expandNthThat (n - 1) sat f xs
    else x : expandNthThat n sat f xs

-- >>> expandNthThat 2 (< 0) (replicate 3) [-2,-1,-4,4,-6,13]
-- [-2,-1,-4,-4,-4,4,-6,13]

isLegal :: (_) => NT a -> Template (ProdRule a) -> Bool
isLegal x = \case
  Template r -> r `elem` legalRule (Right x)
  Comp i α β -> isLegal x α && isLegal (argTypes x α !! (i - 1)) β
  WithRep α m βs -> isLegal x α && and (zipWith isLegal (argTypes x α) (useMeta m α βs))

expandWith :: (a -> Bool) -> [a -> [a]] -> [a] -> [a]
expandWith _ _ [] = []
expandWith _ [] xs = xs
expandWith sat (f : fs) (x : xs) =
  if sat x
    then f x ++ expandWith sat fs xs
    else x : expandWith sat (f : fs) xs

-- >>> expandWith isRight [\(Right x) -> applyRule RProl x] [Left $ TChord V I, Right $ NTChord I I]
-- [Left (TChord V I),Right (NTChord I I),Right (NTChord I I)]

applyTemplate :: (Grammar a) => NT a -> Template (ProdRule a) -> [Symbol a]
applyTemplate x = \case
  Template r -> applyRule r x
  Comp i α β ->
    expandNthThat
      (i - 1)
      isRight
      (\(Right nt) -> applyTemplate nt β)
      (applyTemplate x α)
  WithRep α m βs ->
    expandWith
      isRight
      (do β <- useMeta m α βs; return (\(Right nt) -> applyTemplate nt β))
      (applyTemplate x α)

-- >>> applyTemplate (NTChord I I) (Comp 1 (Comp 2 (Template RProl) (Template RChord)) (Template RChord))
-- [Left (TChord I I),Left (TChord I I)]

growNthThat :: Int -> (a -> Bool) -> (Tree a -> Tree a) -> Tree a -> Tree a
growNthThat n sat f t = applyAt f loc t
  where
    loc = filter (\l -> sat . rootLabel $ navigateTo l t) (leafLocations t) !! n

growWith :: (a -> Bool) -> [Tree a -> Tree a] -> Tree a -> Tree a
growWith sat [] t = t
growWith sat fs t = go fs locs t
  where
    go [] _ t' = t'
    go _ [] t' = t'
    go (f : fs') (loc : ls) t' = go fs' ls (applyAt f loc t')
    locs = filter (\l -> sat . rootLabel $ navigateTo l t) (leafLocations t)

derivedTree :: (Grammar a) => NT a -> Template (ProdRule a) -> Tree (Symbol a)
derivedTree x = \case
  Template r -> Node (Right x) $ (`Node` []) <$> applyRule r x
  Comp i α β ->
    growNthThat
      (i - 1)
      isRight
      (\(Node (Right nt) []) -> derivedTree nt β)
      (derivedTree x α)
  WithRep α m βs ->
    growWith
      isRight
      (do β <- useMeta m α βs; return (\(Node (Right nt) []) -> derivedTree nt β))
      (derivedTree x α)

-- >>> derivedTree (NTChord I I) (Comp 1 (Comp 2 (Template RProl) (Template RChord)) (Template RChord))
-- Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Left (TChord I I), subForest = []}]},Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Left (TChord I I), subForest = []}]}]}

derivedRuleTree :: (Grammar a) => Template (ProdRule a) -> Tree (Maybe (ProdRule a))
derivedRuleTree = \case
  Template r -> Node (Just r) []
  Comp i α β -> undefined

-- outs :: (Grammar a) => Template (ProdRule a) -> NT a
-- outs = error "not implemented outs"

-- mergeTemplate :: (Grammar a) => [Template (ProdRule a)] -> [Template (ProdRule a)]
-- mergeTemplate = error "not implemented mergeTemplate"

-- frontierWithHole :: Int -> [a] -> [[a]]
-- frontierWithHole 0 l = [l]
-- frontierWithHole n l = concat [seg p l | p <- intPartition 2 n]

-- -- >>> frontierWithHole 1 "abcde"
-- -- ProgressCancelledException

-- seg :: [Int] -> [a] -> [[a]]
-- seg ns l = foldr mergeFrontier [] [frontierWithHole n l | n <- ns]

-- -- >>> seg [1,1] "abcde"
-- -- ProgressCancelledException

-- mergeFrontier xs [] = xs
-- mergeFrontier xs ys = init xs ++ [last xs <> head ys] ++ tail ys

-- -- >>> mergeFrontier ["abc","de","l"] ["1234","56","789"]
-- -- ["abc","de","l1234","56","789"]

-- intPartition' :: Int -> Int -> Int -> [[Int]]
-- intPartition' mx k n
--   | n < 0 = []
--   | k == 1, n >= 0, n <= mx = [[n]]
--   | k > 0 = do
--       a <- [0 .. mx]
--       (a :) <$> intPartition' mx (k - 1) (n - a)
--   | otherwise = []

-- intPartition :: Int -> Int -> [[Int]]
-- intPartition mx n = concat [intPartition' mx k n | k <- [0 .. mx]]

-- -- >>> intPartition 2 0
-- -- [[0],[0,0]]