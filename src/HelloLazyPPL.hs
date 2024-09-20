{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module HelloLazyPPL where

import Grammar
import LazyPPL
import LazyPPL.Distributions (categorical, dirichlet)

rulePrior :: (Grammar a) => NT a -> Prob (ProdRule a)
rulePrior x = do
  let alpha r = if r == terminate then 10 else 1
  let rs = legalRule (Right x)
  probs <- dirichlet (alpha <$> rs)
  i <- categorical probs
  return $ rs !! i

priorParseTree :: (Grammar a) => Prob (ParseTree (NT a) (ProdRule a) (T a))
priorParseTree = unfoldParseTreeM rulePrior begin

parseDistr :: (Grammar a) => [T a] -> Meas (ParseTree (NT a) (ProdRule a) (T a))
parseDistr observed = do
  t <- sample priorParseTree
  let predicted = terminals t
  score (if observed == predicted then 0.9 else 0.1)
  return t

parse observed = do
  fws <- mh 1 (parseDistr observed)
  let candidates = map fst $ take 3 $ every 1000 $ drop 10000 fws
  return candidates

-- >>> fmap terminals <$> parse [TChord x I | x <- [VI, II ,V ,I,I, VI, II ,V ,I]]
-- [[TChord I I],[TChord V (I `Of` I),TChord I I,TChord I I,TChord I I],[TChord I I]]

listDiff :: (Eq a) => [a] -> [a] -> Int
listDiff [] [] = 0
listDiff [] ys = length ys
listDiff xs [] = length xs
listDiff (x : xs) (y : ys) =
  if x == y
    then listDiff xs ys
    else 1 + listDiff xs ys
