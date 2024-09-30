{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables,KindSignatures,StandaloneDeriving   #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant lambda" #-}
module HelloMonadBayes where


import           Data.Kind
import           GHC.Float.RealFracMethods (floorDoubleInt)
import           Text.Printf


import           Control.Category
import           Control.Monad.Bayes.Class hiding (generative, likelihood,
                                            prior)
import           Data.Vector               hiding ((++), product, replicate,
                                            replicateM,forM_)
import           Prelude                   hiding (id, (.))
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Inference.Lazy.WIS (lwis)
import Control.Monad.Morph
import Control.Monad.Bayes.Inference.MCMC
import Control.Monad
import Control.Monad.Bayes.Sampler.Strict

data Expr :: Type -> Type where
    Var :: String -> Expr String
    Const :: Int -> Expr Int
    Boolean :: Bool -> Expr Bool
    And :: Expr Bool -> Expr Bool -> Expr Bool
    Pair :: Expr a -> Expr b -> Expr (a, b)

deriving instance Show (Expr a)
deriving instance Eq (Expr a)
deriving instance Ord (Expr a)

data Some f where
    Some :: f a -> Some f




data TypeCases = CaseString | CaseInt | CaseBool | CasePair deriving (Show,Eq,Ord)

distTypeCases :: MonadMeasure m => m TypeCases
distTypeCases = do
    let w = [0.1,0.1,0.4,0.4]
    i <- categorical $ Data.Vector.fromList w
    factor (Exp $ w !! i)
    return ([CaseString,CaseInt,CaseBool,CasePair] !! i)

distSomeExpr :: MonadMeasure m => m (Some Expr)
distSomeExpr = do
    caseType <- distTypeCases
    case caseType of
        CaseString -> Some <$> distExprString
        CaseInt -> Some <$> modelExprInt (5, 1)
        CaseBool -> Some <$> distExprBool 0.2
        CasePair -> do
            Some x <- distSomeExpr
            Some y <- distSomeExpr
            return $ Some (Pair x y)


priorMeanVar :: MonadDistribution m => m (Double, Double)
priorMeanVar = do
    mean <- normal 10 1
    var <- uniform 0 4
    return (mean,var)

modelExprInt :: MonadDistribution m => (Double, Double) -> m (Expr Int)
modelExprInt (mean,var) = do
    Const . floorDoubleInt <$> normal mean var

regressionExprInt :: (MonadMeasure m, Foldable t) => t (Expr Int) -> m (Double, Double)
regressionExprInt obs = do
    (mean,var) <- priorMeanVar
    forM_ obs (\(Const n) -> factor $ Prelude.sum [0.01 * normalPdf mean var t | t <- [(fromIntegral n), fromIntegral n + 0.01 .. (fromIntegral n+1)] ])
    return (mean,var)


regressionExprIntSamples =  replicateM 200 $ sampler (do 
    (mean,var) <- priorMeanVar 
    modelExprInt (15, 2))

-- >>> regressionExprIntSamples
-- [Const 2,Const 3,Const 2,Const 5,Const 5,Const 6,Const 8,Const 3,Const 4,Const 2,Const 7,Const 4,Const 4,Const 5,Const 7,Const 6,Const 0,Const 4,Const 5,Const 4,Const 5,Const 2,Const 5,Const 4,Const 7,Const 9,Const 5,Const 6,Const (-1),Const 6,Const 5,Const 4,Const 6,Const 4,Const 4,Const 9,Const 0,Const 5,Const 5,Const 4,Const 10,Const 4,Const 4,Const 6,Const 5,Const 3,Const 4,Const 4,Const 4,Const 6,Const 3,Const 7,Const 4,Const 5,Const 6,Const 6,Const 5,Const 8,Const 9,Const 4,Const 4,Const 7,Const 3,Const 5,Const 5,Const 4,Const 5,Const 2,Const 2,Const 6,Const 14,Const 5,Const 6,Const 4,Const 8,Const 6,Const 5,Const 4,Const 5,Const 4,Const 6,Const 3,Const 4,Const 4,Const 8,Const 3,Const 4,Const 6,Const 8,Const 6,Const 5,Const 3,Const 4,Const 6,Const 11,Const 7,Const 7,Const 7,Const 9,Const 2]

distExprBool :: MonadMeasure m => Double -> m (Expr Bool)
distExprBool weight = do
    chooseLit <- bernoulli weight
    factor (if chooseLit then 1 else 0)
    if chooseLit then
        Boolean <$> uniformD [True, False]
    else And <$> distExprBool weight <*> distExprBool weight

distExprString :: MonadMeasure m => m  (Expr String)
distExprString = Var <$> uniformD ["X","Y","Z"]





mcmcConfig = MCMCConfig {numMCMCSteps = 100, numBurnIn = 10, proposal = SingleSiteMH}


mhRunsRegression = do 
    obs <- regressionExprIntSamples 
    sampler . unweighted . mcmc mcmcConfig $ regressionExprInt obs

-- >>>mhRunsRegression
-- [(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.399955081084125,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.9971676226945068),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.938198233397635),(11.330244048550755,3.6715899981556643),(11.330244048550755,3.6715899981556643),(11.330244048550755,3.6715899981556643),(11.330244048550755,3.6715899981556643),(11.330244048550755,3.6715899981556643),(11.330244048550755,3.6715899981556643),(11.060373577168107,3.6715899981556643),(11.060373577168107,3.6715899981556643),(11.060373577168107,3.6715899981556643),(11.060373577168107,3.6715899981556643),(11.060373577168107,3.6715899981556643),(11.060373577168107,3.6715899981556643),(9.86611211082362,3.6715899981556643),(9.86611211082362,3.6715899981556643),(9.86611211082362,3.5268028797596354),(9.86611211082362,3.5268028797596354),(9.86611211082362,3.5268028797596354),(9.86611211082362,3.5268028797596354)]
