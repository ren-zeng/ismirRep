{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module PCFG where

import Control.Monad
import Control.Monad.Bayes.Class hiding (independent)
import Control.Monad.Bayes.Enumerator
import Control.Monad.Bayes.Inference.MCMC (mcmc)
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Data.Either
import Data.Function
import Data.List.Extra hiding (product)
import qualified Data.Map as Map (fromList, (!))
import Data.Semiring hiding (fromIntegral)
import Data.Tree
import qualified Data.Vector as V
import Grammar
import Prelude hiding (product, (*))

surface :: Tree a -> [a]
surface (Node x []) = [x]
surface (Node _ ts) = foldMap surface ts

-- | `probDerivation` defines the probability of sampling a
-- derivation when given a joint distribution @p(head=x,rule=r)@
probDerivation ::
  (Monoid b) =>
  (NT a -> ProdRule a -> b) ->
  ParseTree (NT a) (ProdRule a) (T a) ->
  b
probDerivation f = \case
  Leaf x -> mempty
  Branch x r ts -> f x r <> mconcat (probDerivation f <$> ts)

-- | `inferPCFG` infers the rule weights from observed sequences of symbols.
inferPCFG ::
  forall m a.
  (MonadFactor m, ShowGrammar a, _) =>
  [[Symbol a]] ->
  m [(ProdRule a, Double)]
inferPCFG ys = do
  ruleProbs <- ruleProbsPrior
  let densityCat x r = pure $ if r `elem` legalRule (Right x) then Map.fromList ruleProbs Map.! r else 0
  der <- unfoldParseTreeM (ruleDist ruleProbs) begin
  let sur = surface $ valTree der
  forM_ ys (\y -> score (if sur == y then probDerivation densityCat der else 0))
  return ruleProbs

-- | `ruleDist` is the conditional probability @p(rule=r|head=x)@
-- It is parametrized by the rule weights of the PCFG.
ruleDist ::
  (MonadDistribution m, Eq (ProdRule a), Grammar a) =>
  [(ProdRule a, Double)] ->
  NT a ->
  m (ProdRule a)
ruleDist ruleProbs x =
  ruleProbs
    & filter (\(a, b) -> a `elem` legalRule (Right x))
    & categorical'

-- | Sample a sentence from a PCFG parametrized by rule weights
generatePCFG ::
  forall m a.
  (ShowGrammar a, MonadDistribution m, Eq (ProdRule a)) =>
  [(ProdRule a, Double)] ->
  m (ParseTree (NT a) (ProdRule a) (T a))
generatePCFG ruleProbs = do
  unfoldParseTreeM (ruleDist ruleProbs) begin

dirichlet' :: (MonadDistribution m) => ([Double] -> m (V.Vector Double))
dirichlet' = dirichlet . V.fromList

ruleProbsPrior :: forall m a. (_) => m [(ProdRule a, Double)]
ruleProbsPrior = do
  let alpha r = if r == terminate then fromIntegral (length (rules @a)) else 1
  probs <- dirichlet' (alpha <$> rules @a)
  return $ zip rules (V.toList probs)
