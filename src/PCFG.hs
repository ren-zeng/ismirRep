{-# LANGUAGE PartialTypeSignatures,ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes,FlexibleContexts #-}
module PCFG where
import Control.Monad.Bayes.Class
import Grammar
import Data.Tree
import Data.Vector hiding (null, sum, zip, mapM, elem, replicate, length)

import Control.Monad.Bayes.Sampler.Strict
import Data.Kind
import Data.List.Extra



{-
Given (Grammar m a), we want to infer the underlying parameter (i.e. the weight of prod rule conditioned on current symbol)
The parameter is a function of type ('Symbol a -> ProdRule a -> Double') 

- goal1 :: Symbol a -> [Symbol a] -> m (ProdRule a)
+ Given the current symbol (x :: Symbol a) , and the children :: ([Symbol a]), we want to know the distribution of production rule p. 

- goal2 :: [Symbol a] -> m (Symbol a, ProdRule a)
+ Given the children, we want to know the joint probability of (parent :: Symbol a) and (p :: ProdRule a)


            ProdRule a
               |
               V
Symbol a --> Model --> [Symbol a]


-}


{-
PCFG: Each NT is associated with a discrete distribution of production rules (conceptually each rule has a weight) 
    prior for the family of rule probability:
    - N_x ~ condition (legal x n) (Dir [1..n]) 

    the process of elaborating `x : NT` is the following: 
    - sample a production rule `N_x : Int` ~ (Dir [1..n]) * (legal x n) 
    - expand `x` with `N_x` resulting in a list of symbols 

    Q: given an observation of a derivation tree, and the prior of N_x, what is the posterior of N_x?

    Option 1: The derivation tree is of type `Tree ProdRule`. In other words, the nodes are rule-labeled
    
    Q1: Given an observation of a ProdRule applied at `x : NT`, how to update N_x?
    A1= to update the param {w_n} for  dirichlet distribution, we just add 1 to the coresponding w_i. 

    Q3: Given an observation of a surface sequence, how to update N_x?
-}


{-|  
`elaborateM` a single step of (stochastic) rule application to a non-terminal for a PCFG. 
    
- Input: 
    
    `Symbol a -> [Double]` -- A family of distributions on weights of the production rules 
    
    `Symbol a`             -- The input of the production rule.
    
- Output:
    
    `m [Symbol a]`         -- A list of symbols wrapped in a probability monad (Distribution for sampling). Conceptually this is the output of the production rule.
-}
elaborateM ::  (MonadDistribution m, Grammar a) => (NT a -> m (ProdRule a)) -> Symbol a -> m [Symbol a]
elaborateM rDistr x = do
    case x of 
        Left nt -> do 
            r <- rDistr nt
            applyRule r nt
        Right _ -> return []


{-|

`sampleTreeG` samples a derivation tree from a PCFG. It is parametrised by a family of rule distribution indexed by `Symbol a`. 

It represent the conditional distribution: 

P (Tree (Symbol a) | RuleWeights)

-}

-- sampleTreeG :: (MonadDistribution m, Grammar a, _) => (NT a -> [Double]) -> m (Tree (Symbol a))
-- sampleTreeG rDistr = unfoldTreeM g (begin) where
--     g x = do
--         children <- elaborateM rDistr x
--         return (x,children)





-- aTree :: _ =>  m (Tree (Symbol Expr))
-- aTree = sampleTreeG (ruleDistr )

-- t = sampler aTree
-- >>> t
-- Node {rootLabel = NTExpr, subForest = [Node {rootLabel = NTInt, subForest = [Node {rootLabel = TInt 12, subForest = []}]}]}

ruleDistr :: (Grammar  a, _) => NT a -> [Double]
ruleDistr x = (\rule -> if rule `elem` legalRule  x then 1 else 0) <$> rules

summaryRuleDist :: (Grammar  a, Enum (ProdRule a), Bounded (ProdRule a), Eq (ProdRule a), Enum (NT a), Bounded (NT a)) => [(NT a, [(ProdRule a,Double)])]
summaryRuleDist = (\x -> (x, zip (rules) (ruleDistr x) )) <$> enumerate

r ::[(NT Expr, [(ProdRule Expr, Double)])]
r = summaryRuleDist

-- >>> r
-- [(NTExpr,[(RVar,1.0),(RConst,1.0),(RPlus,1.0),(RString,0.0),(RInt,0.0)]),(NTString,[(RVar,0.0),(RConst,0.0),(RPlus,0.0),(RString,1.0),(RInt,0.0)]),(NTInt,[(RVar,0.0),(RConst,0.0),(RPlus,0.0),(RString,0.0),(RInt,1.0)])]
