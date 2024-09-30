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
import Data.Maybe (isNothing)
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
  argTypes :: x -> a -> [b]

instance (Grammar a) => ArgTypes (NT a) (ProdRule a) (Symbol a) where
  argTypes x p = applyRule p x

instance forall a. (Grammar a) => ArgTypes (NT a) (Template (ProdRule a)) (NT a) where
  argTypes x (Template r) = rights $ argTypes @(NT a) @(ProdRule a) @(Symbol a) x r
  argTypes x (Id) = [x]
  argTypes x (WithRep α m βs) = concat $ zipWith (argTypes @(NT a)) (argTypes x α) (useMeta m α βs)

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

isLegal :: (_) => NT a -> Template (ProdRule a) -> Bool
isLegal x = \case
  Template r -> r `elem` legalRule (Right x)
  Id -> True
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
  Id -> [Right x]
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
  IdF -> 0
  WithRepF x _ ys -> x + sum ys
