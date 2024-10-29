{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS -WparseAllCasesall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ParsingTemplateGrammar (baseParse, parseTemplate, parseAllCases) where

import Control.Applicative (asum)
import Control.Monad (guard, zipWithM)
import Control.Monad.Extra (concatMapM)
import Control.Monad.Search
import Data.Bool (bool)
import Data.Either (isRight, lefts)
import Data.Function
import Data.List hiding (product, sum)
import Data.List.Extra (minimumOn, notNull)
import Data.List.Split
import Data.Maybe
import Data.MemoTrie (HasTrie, memoFix)
import Data.Monoid (Sum (Sum, getSum))
import Data.Ord (comparing)
import Data.PartialOrd (minima)
import qualified Data.PartialOrd as POrd
import Debug.Trace (trace)
import GHC.Base hiding (One, Symbol, foldr, mapM)
import GrammarInstances
import Meta
import Preliminaries.Grammar hiding (Plus)
import TemplateGrammar
import Text.Printf
import Prelude

instance (Ord a, Monoid a) => MonadFail (Search a) where
  fail _ = mzero

splitEvidence :: [Either a b] -> [[a]]
splitEvidence = fmap lefts . splitWhen isRight

-- >>> splitEvidence [Left $ TChord V I,Left $ TChord I I, Right $ NTChord V I, Left $ TChord I I,Right $ NTChord I I]
-- [[TChord V I,TChord I I],[TChord I I],[]]

-- | All possible ways to split a list into n part (n>0).
splitsN :: Int -> [a] -> [[[a]]]
splitsN n l
  | n <= 0 = error "the number of chunks should be positive for splitsN "
  | n == 1 = [[l]]
  | n == 2 = zipWith (\a b -> [a, b]) (inits l) (tails l)
  | otherwise = do
      [l1, l2] <- splitsN 2 l
      ls <- splitsN (n - 1) l2
      return (l1 : ls)

evidence :: (Grammar a) => NT a -> Template (ProdRule a) -> Maybe [[T a]]
evidence x t = splitEvidence <$> applyTemplate x t

hasEvidence :: (Grammar a) => NT a -> Template (ProdRule a) -> [[T a]] -> Bool
hasEvidence x t e = evidence x t == Just e

topBy :: (Ord b) => (a -> b) -> [a] -> [a]
topBy f = take 1 . sortBy (comparing f)

heuristic :: NT a -> [[T a]] -> Sum Int
heuristic = undefined

heuristicL :: [[[a]]] -> Sum Int
heuristicL = mempty

-- >>> heuristicL [[[1,2],[4]],[[3]]]
-- Sum {getSum = 0}

type Evidence a = [[a]]

{-
0 = [0] | [0,0]
1 = [1] | [0,1] | [1,0]
2 = [2] | [0,2] | [1,1] | [2,0]
-}

breakDownEvidence' :: (_) => [Int] -> Evidence a -> [(Evidence a, [Evidence a])]
breakDownEvidence' ns e =
  filter
    ( \(_e, _ess) ->
        (e `notElem` _e : _ess)
          && all (\case [_l] -> notNull _l; _ -> True) _ess
    )
    $ case e of
      [l] -> case ns of
        [0] -> do
          [l1, l2, l3] <- splitsN 3 l
          guard (l /= l2)
          return ([l1, l3], [[l2]])
        [0, 0] -> do
          [l1, l2, l3, l4, l5] <- splitsN 5 l
          return ([l1, l3, l5], [[l2], [l4]])
        _ -> mzero
      [l_L, l_R] -> case ns of
        [1] -> do
          [l1, l2] <- splitsN 2 l_L
          [l3, l4] <- splitsN 2 l_R
          return ([l1, l4], [[l2, l3]])
        [0, 1] -> do
          [l1, l2, l3, l4] <- splitsN 4 l_L
          [l5, l6] <- splitsN 2 l_R
          return ([l1, l3, l6], [[l2], [l4, l5]])
        [1, 0] -> do
          [l1, l2] <- splitsN 2 l_L
          [l3, l4, l5, l6] <- splitsN 4 l_R
          return ([l1, l4, l6], [[l2, l3], [l5]])
        _ -> mzero
      [l_L, l_M, l_R] -> case ns of
        [2] -> do
          [l1, l2] <- splitsN 2 l_L
          [l3] <- splitsN 1 l_M
          [l4, l5] <- splitsN 2 l_R
          return ([l1, l5], [[l2, l3, l4]])
        [0, 2] -> do
          [l1, l2, l3, l4] <- splitsN 4 l_L
          [l5] <- splitsN 1 l_M
          [l6, l7] <- splitsN 2 l_R
          return ([l1, l3, l7], [[l2], [l4, l5, l6]])
        [1, 1] -> do
          [l1, l2] <- splitsN 2 l_L
          [l3, l4, l5] <- splitsN 3 l_M
          [l6, l7] <- splitsN 2 l_R
          return ([l1, l4, l7], [[l2, l3], [l5, l6]])
        [2, 0] -> do
          [l1, l2] <- splitsN 2 l_L
          [l3] <- splitsN 1 l_M
          [l4, l5, l6, l7] <- splitsN 4 l_R
          return ([l1, l5, l7], [[l2, l3, l4], [l6]])
        _ -> mzero
      _ -> mzero

-- error $
--   printf
--     "illegal combination of arities and evidence %s %s"
--     (show ns)
--     (show e)

breakDownEvidence e =
  foldSum
    (`breakDownEvidence'` e)
    [[0], [0, 0], [1], [1, 0], [0, 1], [2], [2, 0], [1, 1], [0, 2]]

-- >>> length $ breakDownEvidence  [replicate 10 1]
-- 549

parseTemplate :: (_) => [[T a]] -> NT a -> [Template (ProdRule a)]
parseTemplate = memoFix2 $ parseAllCases

parseAllCases ::
  (m ~ Maybe, Grammar a, Monad m, _) =>
  ([[T a]] -> NT a -> [Template (ProdRule a)]) ->
  [[T a]] ->
  NT a ->
  [Template (ProdRule a)]
parseAllCases f e !x =
  POrd.minima $
    baseParse x e ++ foldMap go (breakDownEvidence e)
  where
    go (_e, _es) = do
      guard (_es /= [[], [], []])
      α <- f _e x
      let Just ts = argTypes x α
      βs <- frugalParse f α (zip ts _es) []
      let (m, βs') = inferMeta α βs
      return $ WithRep α m βs'

frugalParse ::
  (_) =>
  ([[T a]] -> NT a -> m (Template (ProdRule a))) ->
  Template (ProdRule a) ->
  [(NT a, Evidence (T a))] ->
  [Template (ProdRule a)] ->
  m [Template (ProdRule a)]
frugalParse f α xes tps = case xes of
  [] -> return []
  ((x, e) : _xes) -> do
    tp <- go x e
    _tps <- frugalParse f α _xes (tps ++ [tp])
    return (tp : _tps)
  where
    go x e = case find (\t -> hasEvidence x t e) (α : tps) of
      Nothing -> f e x
      Just tp -> return tp

baseParse ::
  (Grammar a, _) =>
  NT a ->
  [[T a]] ->
  [Template (ProdRule a)]
baseParse x ls =
  minima
    ( do
        t <- (Template <$> legalRule (Right x)) <|> return Id
        guard (hasEvidence x t ls)
        return t
    )

memoFix2 f = memoFix (\g a -> memoFix (\h b -> f g a b))

foldSum f = asum . fmap f

-- explainEvidence' ::
--   (Grammar a, _) =>
--   (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
--   NT a ->
--   [[T a]] ->
--   m (Template (ProdRule a))
-- explainEvidence' f x ls =
--   asum
--     [ do
--         cost 1 0
--         baseParse x ls,
--       do
--         -- cost 0 (foldMap (Sum . length) ls)
--         case ls of
--           [[], [], []] -> empty
--           [l] -> zeroHoleParse f x l
--           [l1, l2] -> oneHoleParse f x l1 l2
--           [l1, l2, l3] -> twoHoleParse f x l1 l2 l3
--           _ -> empty
--     ]

-- explainEvidence'' ::
--   (Grammar a, _) =>
--   ([[T a]] -> NT a -> m (Template (ProdRule a))) ->
--   [[T a]] ->
--   NT a ->
--   m (Template (ProdRule a))
-- explainEvidence'' f ls x = explainEvidence' (flip f) x ls

-- -- | Parsing for template grammar
-- explainEvidence ::
--   (Grammar a, MonadPlus m, HasTrie (NT a), HasTrie (T a), _) =>
--   [[T a]] ->
--   NT a ->
--   m (Template (ProdRule a))
-- explainEvidence = memoFix2 explainEvidence''

-- zeroHoleParse ::
--   (MonadPlus m, Grammar a, _) =>
--   (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
--   NT a ->
--   [T a] ->
--   m (Template (ProdRule a))
-- zeroHoleParse f x l =
--   asum
--     [ foldSum
--         ( \(l1, l2, l3, l4, l5) -> do
--             α <- f x [l1, l3, l5]
--             let Just [y, z] = argTypes x α
--             β <- f y [l2]
--             asum
--               [ do
--                   guard $ hasEvidence z β [l4]
--                   cost 0 $ heuristicL [[l1, l3, l5], [l2]]
--                   return $ WithRep α [New, RepLoc 1] [β],
--                 do
--                   γ <- f z [l4]
--                   guard $ γ /= β
--                   cost 0 $ heuristicL [[l1, l3, l5], [l2], [l4]]
--                   return $ WithRep α [New, New] [β, γ]
--               ]
--         )
--         ( do
--             [l1, l2, l3, l4, l5] <- splitsN 5 l
--             guard (l `notElem` [l2, l4])
--             guard (notNull l2)
--             guard (notNull l4)
--             return (l1, l2, l3, l4, l5)
--         ),
--       foldSum
--         ( \(l1, l2, l3) -> do
--             α <- f x [l1, l3]
--             let Just [y] = argTypes x α
--             β <- f y [l2]
--             cost 0 $ heuristicL [[l1, l3], [l2]]
--             return (WithRep α [New] [β])
--         )
--         ( do
--             [l1, l2, l3] <- splitsN 3 l
--             guard (l2 /= l)
--             guard (notNull l2)
--             return (l1, l2, l3)
--         )
--     ]

-- oneHoleParse ::
--   (MonadPlus m, Grammar a, _) =>
--   (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
--   NT a ->
--   [T a] ->
--   [T a] ->
--   m (Template (ProdRule a))
-- oneHoleParse f x l_L l_R =
--   asum
--     [ foldSum
--         ( \(l1, l2, l3, l4) -> do
--             α <- f x [l1, l3, l4]
--             let Just [y, _] = argTypes x α
--             β <- f y [l2]
--             cost 0 $ heuristicL [[l1, l3, l4], [l2]]
--             return $ WithRep α [New, New] [β, Id]
--         )
--         ( do
--             [l1, l2, l3] <- splitsN 3 l_L
--             let l4 = l_R
--             guard (notNull l2)
--             return (l1, l2, l3, l4)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4) -> do
--             α <- f x [l1, l2, l4]
--             let Just [_, z] = argTypes x α
--             β <- f z [l3]
--             cost 0 $ heuristicL [[l1, l2, l4], [l3]]
--             return $ WithRep α [New, New] [Id, β]
--         )
--         ( do
--             [l2, l3, l4] <- splitsN 3 l_R
--             guard (notNull l3)
--             let l1 = l_L
--             return (l1, l2, l3, l4)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4) -> do
--             α <- f x [l1, l4]
--             let Just [y] = argTypes x α
--             asum
--               [ do
--                   guard $ hasEvidence y α [l2, l3]
--                   cost 0 $ heuristicL [[l1, l4]]
--                   return $ WithRep α [Star] [],
--                 do
--                   β <- f y [l2, l3]
--                   guard $ β /= α
--                   cost 0 $ heuristicL [[l1, l4], [l2, l3]]
--                   return $ WithRep α [New] [β]
--               ]
--         )
--         ( do
--             [l1, l2] <- splitsN 2 l_L
--             [l3, l4] <- splitsN 2 l_R
--             guard ([l1, l4] /= [l_L, l_R])
--             guard ([l2, l3] /= [l_L, l_R])
--             return (l1, l2, l3, l4)
--         )
--     ]

-- twoHoleParse ::
--   (MonadPlus m, Grammar a, _) =>
--   (NT a -> [[T a]] -> m (Template (ProdRule a))) ->
--   NT a ->
--   [T a] ->
--   [T a] ->
--   [T a] ->
--   m (Template (ProdRule a))
-- twoHoleParse f x l_L l_M l_R =
--   asum
--     [ foldSum
--         ( \(l1, l2, l3, l4, l5, l6, l7) -> do
--             α <- f x [l1, l5, l7]
--             let Just [y, z] = argTypes x α
--             β <- f z [l6]
--             asum
--               [ do
--                   guard (hasEvidence y α [l2, l3, l4])
--                   cost 0 $ heuristicL [[l1, l5, l7], [l6]]
--                   return $ WithRep α [Star, New] [β],
--                 do
--                   β1 <- f y [l2, l3, l4]
--                   guard (β /= β1)
--                   cost 0 $ heuristicL [[l1, l5, l7], [l6], [l2, l3, l4]]
--                   return $ WithRep α [New, New] [β1, β]
--               ]
--         )
--         ( do
--             [l1, l2] <- splitsN 2 l_L
--             let l3 = l_M
--             [l4, l5, l6, l7] <- splitsN 4 l_R
--             guard (notNull l6)
--             guard ([l_L, l_M, l_R] `notElem` [[l1, l5, l7], [l2, l3, l4]])
--             return (l1, l2, l3, l4, l5, l6, l7)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4, l5, l6, l7) -> do
--             α <- f x [l1, l3, l7]
--             let Just [y, z] = argTypes x α
--             β <- f y [l2]
--             asum
--               [ do
--                   guard $ hasEvidence z α [l4, l5, l6]
--                   cost 0 $ heuristicL [[l1, l3, l7], [l2]]
--                   return $ WithRep α [New, Star] [β],
--                 do
--                   β1 <- f z [l4, l5, l6]
--                   guard $ β1 /= α
--                   cost 0 $ heuristicL [[l1, l3, l7], [l2], [l4, l5, l6]]
--                   return $ WithRep α [New, New] [β, β1]
--               ]
--         )
--         ( do
--             [[l1, l2, l3, l4], [l5], [l6, l7]] <- zipWithM splitsN [4, 1, 2] [l_L, l_M, l_R]
--             guard ([l_L, l_M, l_R] `notElem` [[l1, l3, l7], [l4, l5, l6]])
--             guard (notNull l2)
--             return (l1, l2, l3, l4, l5, l6, l7)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4, l5) -> do
--             α <- f x [l1, l4, l5]
--             let Just [y, _] = argTypes x α
--             β <- f y [l2, l3]
--             cost 0 $ heuristicL [[l1, l4, l5], [l2, l3]]
--             return $ WithRep α [New, New] [β, Id]
--         )
--         ( do
--             [[l1, l2], [l3, l4], [l5]] <- zipWithM splitsN [2, 2, 1] [l_L, l_M, l_R]
--             guard ([l_L, l_M, l_R] /= [l1, l4, l5])
--             return (l1, l2, l3, l4, l5)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4, l5) -> do
--             α <- f x [l1, l2, l5]
--             let Just [_, z] = argTypes x α
--             β <- f z [l3, l4]
--             cost 0 $ heuristicL [[l1, l2, l5], [l3, l4]]
--             return $ WithRep α [New, New] [Id, β]
--         )
--         ( do
--             [[l1], [l2, l3], [l4, l5]] <- zipWithM splitsN [1, 2, 2] [l_L, l_M, l_R]
--             guard ([l_L, l_M, l_R] /= [l1, l2, l5])
--             return (l1, l2, l3, l4, l5)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4, l5) -> do
--             α <- f x [l1, l5]
--             let Just [y] = argTypes x α
--             β <- f y [l2, l3, l4]
--             cost 0 $ heuristicL [[l1, l5], [l2, l3, l4]]
--             return $ WithRep α [New] [β]
--         )
--         ( do
--             [[l1, l2], [l3], [l4, l5]] <- zipWithM splitsN [2, 1, 2] [l_L, l_M, l_R]
--             return (l1, l2, l3, l4, l5)
--         ),
--       foldSum
--         ( \(l1, l2, l3, l4, l5, l6, l7) -> do
--             α <- f x [l1, l4, l7]
--             let Just [y, z] = argTypes x α
--             β <- f y [l2, l3]
--             asum
--               [ do
--                   guard $ hasEvidence z β [l5, l6]
--                   cost 0 $ heuristicL [[l1, l4, l7], [l2, l3]]
--                   return $ WithRep α [New, RepLoc 1] [β],
--                 do
--                   γ <- f z [l5, l6]
--                   guard $ γ /= β
--                   cost 0 $ heuristicL [[l1, l4, l7], [l2, l3], [l5, l6]]
--                   return $ WithRep α [New, New] [β, γ]
--               ]
--         )
--         ( do
--             [[l1, l2], [l3, l4, l5], [l6, l7]] <- zipWithM splitsN [2, 3, 2] [l_L, l_M, l_R]
--             guard ([l_L, l_M, l_R] /= [l1, l4, l7])
--             return (l1, l2, l3, l4, l5, l6, l7)
--         )
--     ]
