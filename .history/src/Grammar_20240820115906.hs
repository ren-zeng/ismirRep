{-# LANGUAGE AllowAmbiguousTypes,ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE PartialTypeSignatures,DeriveDataTypeable,ConstrainedClassMethods,FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ConstraintKinds #-}

module Grammar where
import           Control.Monad.Bayes.Class
import           Data.Data
import Text.Printf
import Data.Tree ( Tree(Node, rootLabel), unfoldTreeM,drawTree )
import Data.Vector hiding (take,sequence, filter, foldMap, foldl, foldM, foldr, replicate, mapM, length, zip,replicateM)
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Control.Monad
import Control.Monad.Bayes.Weighted (weightedT, unweighted, runWeightedT)
import Control.Monad.Bayes.Enumerator (toEmpirical)
import Control.Monad.Bayes.Inference.MCMC
import Data.Function
import Control.Arrow
import Data.Kind
import Data.Either






type Symbol a = Either  (T a) (NT a)

type ShowGrammar a  = (Grammar a, Show (NT a),Show (ProdRule a), Show (T a))


class Grammar a where
    data NT a
    data T a
    data ProdRule a

    decode :: Tree (ProdRule a) -> Maybe a
    encode :: a -> Tree (ProdRule a)

    ruleName :: ProdRule a -> String
    begin :: Symbol a
    legalRule :: Symbol a -> [ProdRule a]
    nArg :: ProdRule a -> Int
    
    safeApplyRule :: ProdRule a -> NT a -> Maybe [Symbol a]

    applyRule :: (Show (ProdRule a), Show (NT a)) => ProdRule a -> NT a -> [Symbol a]
    applyRule x y = case safeApplyRule x y of
        Nothing -> error (printf "wrong type match: cannot apply rule %s to %s" (show x) (show y))
        Just r -> r

    nts :: (Enum (NT a), Bounded (NT a)) => [NT a]
    nts = enumFrom minBound

    rules :: (Enum (ProdRule a), Bounded (ProdRule a)) => [ProdRule a]
    rules = enumFrom minBound

    possibleMerges :: [Symbol a] -> [(NT a, ProdRule a)]

    terminate :: ProdRule a
    




mergeRule :: (Grammar a,_) => [Symbol a] -> [(NT a, ProdRule a)]
mergeRule xs = filter (\(x,r) -> safeApplyRule r x == Just xs) [(x,p) | x <- nts, p <- legalRule (Right x)]


-- >>> mergeRule [Left $ NTString]
-- [(NTExpr,RVar)]

-- >>> mergeRule [Right $ TString "x"]
-- [(NTString,RString)]



updateChoiceWeights :: _ => [b] -> b -> [Double] -> [Double]
updateChoiceWeights rules obsRule weights = [if x == obsRule then i+1 else i | (i,x) <- zip weights rules]

updatRuleProb :: _ => Tree (a,b) -> (a -> [b]) -> a -> [Double] -> [Double]
updatRuleProb t getRules _ weights = foldr go weights t
    where go (x,r) = updateChoiceWeights (getRules x) r

inferRuleTree :: (a -> [a] -> Maybe b) -> Tree a -> Tree (a,Maybe b)
inferRuleTree f (Node x ts) = Node (x, f x (rootLabel <$> ts)) (inferRuleTree f <$> ts)


growTree :: (a -> [a]) -> a -> Tree a
growTree f x = Node x $ growTree f <$> f x





growTreeM :: (Monad m) => (a -> m [a]) -> a -> m (Tree a)
growTreeM sprout seed = do
    branches <- sprout seed
    subtrees <- mapM (growTreeM sprout) branches
    return $ Node seed subtrees



toCategorical :: (MonadDistribution m) => [m a] -> m a
toCategorical l = do
    weight <- distWeights (length l)
    i <- categorical $ fromList weight
    l !! i

distWeights :: MonadDistribution m => Int -> m [Double]
distWeights n = toList <$> dirichlet (fromList (replicate n (1 / fromIntegral n)))




-- elaboratePost :: forall m a. (MonadDistribution m, Grammar m a, _) => [Symbol a] -> Symbol a -> m [Double] -> m [Double]
-- elaboratePost xs x priorW = 
--     case findRule x xs of
--         Nothing -> priorW
--         Just rule -> updateChoiceWeights (legalRule @m x) rule <$> priorW


distSymbol = undefined






data Expr
    = Var String
    | Const Int
    | Expr `Plus` Expr
    | Expr `Mult` Expr
    deriving (Show,Data,Eq,Ord)

instance Grammar Expr where

    data NT Expr
        = NTExpr
        | NTString
        | NTInt
        deriving (Show,Enum,Ord,Bounded,Eq)

    data T Expr
        = TString String
        | TInt Int
        deriving (Show,Eq,Ord)

    data ProdRule Expr
        = RVar
        | RConst
        | RPlus
        | RMult
        | RString
        | RInt
        deriving (Show,Enum,Ord,Bounded,Eq)

    encode = \case
        Var x -> Node RVar []
        Const x -> Node RConst []
        e1 `Plus` e2 -> Node RPlus [encode e1, encode e2]
        e1 `Mult` e2 -> Node RMult [encode e1, encode e2]

    decode (Node x ts) = case (x,ts) of
        (RVar,[]) -> Just (Var "x")
        (RConst,[]) -> Just (Const 0)
        (RPlus, [t1,t2]) -> Plus <$> decode t1 <*> decode t2
        (RMult, [t1,t2]) -> Mult <$> decode t1 <*> decode t2
        _ -> Nothing

    ruleName = show

    begin = Right NTExpr

    legalRule = \case
        Right NTExpr      -> [RVar, RConst, RPlus, RMult]
        Right NTInt       -> [RInt]
        Right NTString    -> [RString]
        Left _          -> []



    -- argSymbol x = Left <$> case x of
    --     RVar        -> [NTString]
    --     RConst      -> [NTInt]
    --     RPlus       -> [NTExpr, NTExpr]
    --     RMult       -> [NTExpr, NTExpr]
    --     RString     -> []
    --     RInt        -> []

    safeApplyRule RString NTString = Just $ Left <$> [TString "x"]
    safeApplyRule RInt NTInt = Just $ Left <$> [TInt 42]
    safeApplyRule RVar NTExpr =  Just $ [Right NTString]
    safeApplyRule RConst NTExpr = Just $ [Right NTInt]
    safeApplyRule RPlus NTExpr =  Just $ Right <$> [NTExpr, NTExpr]
    safeApplyRule RMult NTExpr =  Just $ Right <$> [NTExpr, NTExpr]
    safeApplyRule _ _ = Nothing

    














type family Vof (x:: Numeral) :: Numeral where
    Vof I = V
    Vof II = VI
    Vof III = VII
    Vof IV = I
    Vof V = II
    Vof VI = III
    Vof VII = IV

data Numeral = I | II | III | IV | V | VI | VII
    | Numeral `Of` Numeral
    deriving (Show,Eq,Ord)

isOf :: Numeral -> Bool
isOf (_ `Of` _) = True
isOf _ = False

vof :: Numeral -> Numeral
vof I = V
vof II = VI
vof III = VII
vof IV = I
vof V = II
vof VI = III
vof VII = IV



data Chord :: Numeral -> Numeral -> Type where
    Chord :: Chord x y
    D5 :: Chord (Vof x) y -> Chord x y -> Chord x y
    AppD :: Chord V (x `Of` y) -> Chord I (x `Of` y) -> Chord x y
    IV_V :: Chord IV y -> Chord V y -> Chord V y

ofKey :: Numeral -> Numeral -> T (Chord x y)
x `ofKey` y = TChord x y

instance Grammar (Chord x y) where
    data T (Chord x y)
        = TChord Numeral Numeral
        deriving (Show,Ord,Eq)

    
    data NT (Chord x y)
        = NTChord Numeral Numeral
        deriving (Show,Eq)

    data ProdRule (Chord x y)
        = RChord
        | RProl
        | RD5
        | RAppD
        | RIV_V
        deriving (Show,Enum,Ord,Bounded,Eq)

    ruleName = show

    begin = Right $ NTChord I I
    
    nArg = \case 
        RChord -> 1
        RProl -> 2
        RD5 -> 2  
        RAppD -> 2 
        RIV_V -> 2

    legalRule (Right (NTChord V y)) =  [RChord, RProl,RD5, RAppD, RIV_V]
    legalRule (Right (NTChord x y)) =  [RChord, RProl,RD5, RAppD]
    legalRule (Left _) = []

    decode = undefined
    encode = undefined
    safeApplyRule RChord (NTChord x y) = Just $ Left <$> [TChord x y]
    safeApplyRule RProl (NTChord x y) = Just $ Right <$> [NTChord x y,NTChord x y]
    safeApplyRule RD5 (NTChord x y) = Just $ Right <$> [NTChord (vof x) y, NTChord x y]
    safeApplyRule RAppD (NTChord x y) = Just $ Right <$> [NTChord V (x `Of` y), NTChord x y]
    safeApplyRule RIV_V (NTChord x y) 
        | x == V = Just $ Right <$> [NTChord IV y,NTChord V y]
        | otherwise = Nothing


    possibleMerges [Right (NTChord x y), Right (NTChord x' y')] = if 
        | (x,y) == (x',y') -> [(NTChord x y,RProl)]
        | y == y', x == vof x' -> [(NTChord x' y', RD5)]
        | y == y', (x,x') == (IV,V) -> [(NTChord x' y', RIV_V)]
        | otherwise -> case y of 
            a `Of` b -> if 
                | (a,b) == (x',y'), x == V -> [(NTChord a b, RAppD)] 
                | otherwise -> []
            _ -> []
    possibleMerges [Left (TChord x y)] = [(NTChord x y, RChord)]
    possibleMerges _ = []

    terminate = RChord
    
            

-- >>> safeApplyRule RAppD (NTChord V V)
-- Just [Left (NTChord V (V `Of` V)),Left (NTChord I (V `Of` V))]


-- instance (MonadDistribution m) => PGrammar m Chord where




--     applyRule RChord (TChord x y) = return [TNumeral x y]
--     applyRule RD5 (TChord x y) = return [TChord (vof x) y, TChord x y]
--     applyRule RAppD (TChord x y) = return [TChord V (x `Of` y), TChord I (x `Of` y)]
--     applyRule RIV_V (TChord V y) = return [TChord IV y, TChord V y]
--     applyRule _ _ = return []




mcmcConfig = MCMCConfig {numMCMCSteps = 200, numBurnIn = 100, proposal = SingleSiteMH}


sampleTree :: (Grammar a,MonadDistribution m,_) => m (NT a -> ProdRule a) -> Symbol a -> m (Tree (Symbol a))
sampleTree d x@(Left _) = return (Node x [])
sampleTree d x@(Right nt) = do
    ruleDist <- d
    let rule = ruleDist nt
    let xs = applyRule rule nt
    subTrees <- mapM (sampleTree d) xs
    return $ Node x subTrees

data ParseTree a b = Leaf a | Branch a b [ParseTree a b] 
    deriving (Show,Eq)

unfoldParseTreeM :: (MonadDistribution m, ShowGrammar a)
    => (NT a -> m (ProdRule a)) 
    -> Symbol a 
    -> m (ParseTree (Symbol a) (ProdRule a))
unfoldParseTreeM  sampleRule = \case 
    x@(Left _) -> return $ Leaf x 
    x@(Right nt) -> do 
        r <- sampleRule nt 
        let xs = applyRule r nt 
        ts <- unfoldParseTreeM sampleRule `mapM` xs
        return $ Branch x r ts

testUnfold = sampler $ unfoldParseTreeM chordRuleDistPrior (Right $ NTChord I I)

-- >>> testUnfold
-- Branch (Right (NTChord I I)) RChord [Leaf (Left (TChord I I))]

ruleTree :: ParseTree a b -> Tree (Maybe b)
ruleTree = \case 
    Leaf x -> Node Nothing [] 
    Branch _ r ts -> Node (Just r) (ruleTree <$> ts)

valTree :: ParseTree a b -> Tree a
valTree = \case 
    Leaf x -> Node x [] 
    Branch x _ ts -> Node x (valTree <$> ts)

nodeVal :: ParseTree a b -> a
nodeVal = \case 
    Leaf x -> x
    Branch x _ _ -> x


categorical' :: MonadDistribution m => [(a,Double)] -> m a
categorical' xs = do
    let weights = snd <$> xs
        choices = fst <$> xs
    n <- categorical $ fromList weights
    return (choices !! n)

-- >>> replicateM 20 $ sampler $ categorical' [("A",0.4), ("B",0.1),("C",0.1),("D",0.1),("E",0.1)]
-- ["D","C","C","C","A","A","A","B","C","A","E","A","E","A","A","A","C","B","C","A"]

chordRuleDistPrior :: _ => NT (Chord x y) -> m (ProdRule (Chord x y))
chordRuleDistPrior = \case 
    NTChord x y -> categorical' [(RChord,0.5),(RAppD,0.1),(RD5, 0.1), (RProl,0.1)] 
