{-# LANGUAGE PartialTypeSignatures,ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes,FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module PCFG where
import Control.Monad.Bayes.Class hiding (independent)
import Grammar
import Data.Tree
import Data.List.Extra hiding (product)
import Control.Monad
import Control.Monad.Bayes.Inference.Lazy.MH (mh)
import Data.Semiring hiding (fromIntegral)
import Prelude hiding ((*), product)
import Data.Map (fromList, (!))
import qualified Data.Vector as V
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Control.Monad.Bayes.Enumerator (enumerator)
import Control.Monad.Bayes.Inference.MCMC (mcmc, mcmcBasic)


surface :: Tree a -> [a]
surface (Node x []) = [x]
surface (Node _ ts) = foldMap surface ts

probDerivation :: (Monoid b) =>
    (Symbol a -> ProdRule a -> b)
    -> ParseTree (Symbol a) (ProdRule a)
    -> b
probDerivation f = \case
    Leaf x -> mempty
    Branch x r ts -> f x r <> mconcat (probDerivation f <$> ts)


inferPCFG ::forall m a. (MonadFactor m, ShowGrammar a,_)
    => [[Symbol a]]
    -> m (V.Vector Double)
inferPCFG ys = do
    probs <- dirichlet $ V.fromList 
        ((\r -> if r == terminate then fromIntegral (length (rules @a)) else 1) 
        <$> rules @a) 
    let ruleProbs = zip (rules @a) (V.toList probs)
        ruleDist x = categorical' (filter (\(a,b) -> a `elem` legalRule (Right x)) ruleProbs)
        densityCat x r = pure $ if r `elem` legalRule x then fromList ruleProbs ! r else 0
    der <- unfoldParseTreeM ruleDist begin
    let sur = surface $ valTree der
    forM_ ys (\y -> score (if sur == y then probDerivation densityCat der else 0) ) 
    return probs

generatePCFG :: forall m a. _ => m _
generatePCFG = do 
    probs <- dirichlet $ V.fromList 
        ((\r -> if r == terminate then fromIntegral (length (rules @a)) else 1) 
        <$> rules @a) 
    let ruleProbs = zip (rules @a) (V.toList probs)
        ruleDist x = categorical' (filter (\(a,b) -> a `elem` legalRule (Right x)) ruleProbs) 
    der <- unfoldParseTreeM ruleDist begin
    let sur = surface $ valTree der 
    return probs


-- >>> sampler $ generatePCFG @_ @(Chord _ _)
-- ProgressCancelledException

testInference :: _ => _
testInference = inferPCFG $
    fmap (Left . uncurry TChord) <$> replicate 1000 [(I,I)]

infer = sampler $ head . take 1000 <$> mcmc mcmcConfig testInference
-- >>> infer
-- index out of bounds (4,4)

