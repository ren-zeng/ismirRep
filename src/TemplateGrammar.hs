{-# LANGUAGE BlockArguments #-}
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
import Data.Either
import Data.Functor.Foldable
import Data.Functor.Foldable.TH (makeBaseFunctor)
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.Semiring hiding ((-))
import Data.Tree
import GrammarInstances
import Meta
import Preliminaries.Grammar
import TreeUtils
import Prelude hiding (sum, (+))

data Template a
  = Id
  | Template a
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
  arity (Id) = 1
  arity (WithRep a m as) = sum $ arity <$> useMeta m a as

class ArgTypes x a b where
  argTypes :: x -> a -> Maybe [b]

instance (Grammar a) => ArgTypes (NT a) (ProdRule a) (Symbol a) where
  argTypes x p = safeApplyRule p x

instance forall a. (Grammar a) => ArgTypes (NT a) (Template (ProdRule a)) (NT a) where
  argTypes x t = rights <$> applyTemplate x t

-- >>> useMeta [Star,New] (Template RD5) [Template RProl]
-- [Template RD5,Template RProl]

nRule :: Template (ProdRule a) -> Int
nRule = cata $ \case
  TemplateF _ -> 1
  IdF -> 1
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

isLegal :: (Grammar a) => NT a -> Template (ProdRule a) -> Bool
isLegal x t = isJust (applyTemplate x t)

-- >>> isLegal (NTChord I I) (WithRep (Template D5) [New,RepLoc 1] [Template IV_V])
-- False

expandWith :: (a -> Bool) -> [a -> [a]] -> [a] -> [a]
expandWith _ _ [] = []
expandWith _ [] xs = xs
expandWith sat (f : fs) (x : xs) =
  if sat x
    then f x ++ expandWith sat fs xs
    else x : expandWith sat (f : fs) xs

-- >>> expandWith isRight [\(Right x) -> applyRule RProl x] [Left $ TChord V I, Right $ NTChord I I]
-- [Left (TChord V I),Right (NTChord I I),Right (NTChord I I)]

expandWithM :: (Applicative m) => (a -> Bool) -> [a -> m [a]] -> [a] -> m [a]
expandWithM _ _ [] = pure []
expandWithM _ [] xs = pure xs
expandWithM sat (f : fs) (x : xs) =
  if sat x
    then (++) <$> f x <*> expandWithM sat fs xs
    else (x :) <$> expandWithM sat (f : fs) xs

applyTemplate :: (Grammar a) => NT a -> Template (ProdRule a) -> Maybe [Symbol a]
applyTemplate x = \case
  Template r -> safeApplyRule r x
  Id -> Just $ [Right x]
  WithRep α m βs -> case (applyTemplate x α) of
    Nothing -> Nothing
    Just ss -> expandWithM isRight ((\t (Right nt) -> applyTemplate nt t) <$> useMeta m α βs) ss

-- (applyTemplate x α)
-- do
-- ss <- applyTemplate x α
-- let nts = rights ss
-- let r = zipWith ($) (flip applyTemplate <$> useMeta m α βs) nts
-- if all isJust r
--   then return $ concat $ catMaybes r
--   else Nothing

-- sss <- sequence r
-- return $ concat sss

-- >>> applyTemplate (NTChord I I)  (WithRep (Template D5) [Star,New] [Template D5])
-- Just [Right (NTChord II I),Right (NTChord V I),Right (NTChord V I),Right (NTChord I I)]

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
  Id -> Node (Right x) []
  WithRep α m βs ->
    growWith
      isRight
      (do β <- useMeta m α βs; return (\(Node (Right nt) []) -> derivedTree nt β))
      (derivedTree x α)

derivedRuleTree :: forall a. (Grammar a) => Template (ProdRule a) -> Tree (Maybe (ProdRule a))
derivedRuleTree = \case
  Template r -> Node (Just r) $ replicate (nArg r) (Node Nothing [])
  Id -> Node Nothing []
  WithRep α m βs ->
    growWith
      isNothing
      (do β <- useMeta m α βs; return (\(Node Nothing []) -> derivedRuleTree β))
      (derivedRuleTree α)

-- >>> derivedTree (NTChord I I) (Comp 1 (Comp 2 (Template RProl) (Template RChord)) (Template RChord))
-- Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Left (TChord I I), subForest = []}]},Node {rootLabel = Right (NTChord I I), subForest = [Node {rootLabel = Left (TChord I I), subForest = []}]}]}

templateSize :: Template a -> Int
templateSize = cata $ \case
  TemplateF _ -> 1
  IdF -> 1
  WithRepF x _ ys -> 1 + x + sum ys
