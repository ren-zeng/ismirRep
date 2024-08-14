{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
module CYKParser where
import Data.Tree
import Grammar
import Data.List (inits, tails)
import Control.Arrow
import Data.List.NonEmpty (nonEmpty)
import Data.List.Extra (notNull)

data ParseTree a b = Leaf a | Branch a b [ParseTree a b] 
    deriving (Show,Eq)

ruleTree :: ParseTree a b -> Tree (Maybe b)
ruleTree = \case 
    Leaf x -> Node Nothing [] 
    Branch _ r ts -> Node (Just r) (ruleTree <$> ts)

nodeVal :: ParseTree a b -> a
nodeVal = \case 
    Leaf x -> x
    Branch x _ _ -> x

-- >>> length  (parseCYK $ Right . uncurry TChord <$> [(I,I),(V,I),(I,I),(I,I),(I,I)])
-- 9

-- >>> mergeRule $ Left <$> [NTExpr,NTExpr]
-- [(NTExpr,RPlus),(NTExpr,RMult)]
parseCYK :: _ => [Symbol a] -> [ParseTree (Symbol a) (ProdRule a)]
parseCYK [] = []
parseCYK sur = 
    case possibleMerges sur of 
        [] -> do
            (l,r) <- splits sur
            treeL <- parseCYK l
            treeR <- parseCYK r
            mergePTree [treeL,treeR]
        merges -> do
            (root,p) <- merges
            return $ Branch (Left root) p (Leaf <$> sur)

mergePTree :: _ => [ParseTree (Symbol a) (ProdRule a)] -> [ParseTree (Symbol a) (ProdRule a)]
mergePTree xs = do 
    (root,p) <- possibleMerges $ nodeVal <$> xs
    return $ Branch (Left root) p xs

mergeSymbols :: _ => [Symbol a] -> [ParseTree (Symbol a) (ProdRule a)]
mergeSymbols xs = do 
    (root,p) <- possibleMerges xs
    return $ Branch (Left root) p (Leaf <$> xs)

{-
[a] -> PTree a b
goal : [PTree a b] -> PTree a b
-}

insertTree :: ParseTree a b -> ParseTree a b -> ParseTree a b 
insertTree t (Leaf x) = t
insertTree t (Branch x r ts) = Branch x r (zipWith insertTree [t] ts)


splits :: [a] -> [([a], [a])]
splits xs = filter (\(a,b) -> notNull a && notNull b) $ zip (inits xs) (tails xs)

-- >>> splits [1,2]
-- [([1],[2])]

-- >>>  parseCYK [Right $ TString "x", Right $ TString "x"]
-- []

-- >>>  parseCYK [Left NTInt,Left NTInt]
-- [Branch (Left NTExpr) RPlus [Branch (Left NTExpr) RConst [Leaf (Left NTInt)],Branch (Left NTExpr) RConst [Leaf (Left NTInt)]],Branch (Left NTExpr) RMult [Branch (Left NTExpr) RConst [Leaf (Left NTInt)],Branch (Left NTExpr) RConst [Leaf (Left NTInt)]]]


testListMonad xs  = do 
    (l,r) <- splits xs 
    return (l,r,r)

-- >>> testListMonad [1,2,3,4,5] 
-- [([1],[2,3,4,5],[2,3,4,5]),([1,2],[3,4,5],[3,4,5]),([1,2,3],[4,5],[4,5]),([1,2,3,4],[5],[5])]
