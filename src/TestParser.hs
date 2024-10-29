{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module TestParser where

import CYKParser (parseCYK)
import Control.Applicative
import Control.Monad.Fix
import Control.Monad.Search
import Data.Either
import Data.Foldable (minimumBy)
import Data.Functor.Foldable
import Data.List.Extra (maximumOn, minimumOn, nub, sortOn)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Semigroup
import Data.Tree
import Diagrams
import Diagrams.Prelude (Min (getMin), white)
import GrammarInstances
import Meta
import ParsingTemplateGrammar
import Preliminaries.Grammar
import Preliminaries.TreeVisualizer (toTreeDiagram', treeDiagram', writeSVG)
import Preliminaries.Viz
import TemplateGrammar
import Text.Printf

testParse = minimumOn depth . parseCYK $ fmap (`TChord` I) $ concat . replicate 3 $ [I, II, V, I, V, I]
  where
    depth = cata $ \case
      LeafF _ -> 0
      BranchF _ _ ns -> maximum ns + 1

-- >>> testParse
-- Branch (NTChord I I) Prol [Branch (NTChord I I) Prol [Branch (NTChord I I) Chord [Leaf (TChord I I)],Branch (NTChord I I) Prol [Branch (NTChord I I) D5 [Branch (NTChord V I) D5 [Branch (NTChord II I) Chord [Leaf (TChord II I)],Branch (NTChord V I) Chord [Leaf (TChord V I)]],Branch (NTChord I I) Chord [Leaf (TChord I I)]],Branch (NTChord I I) D5 [Branch (NTChord V I) Chord [Leaf (TChord V I)],Branch (NTChord I I) Prol [Branch (NTChord I I) Chord [Leaf (TChord I I)],Branch (NTChord I I) Chord [Leaf (TChord I I)]]]]],Branch (NTChord I I) Prol [Branch (NTChord I I) Prol [Branch (NTChord I I) D5 [Branch (NTChord V I) D5 [Branch (NTChord II I) Chord [Leaf (TChord II I)],Branch (NTChord V I) Chord [Leaf (TChord V I)]],Branch (NTChord I I) Chord [Leaf (TChord I I)]],Branch (NTChord I I) D5 [Branch (NTChord V I) Chord [Leaf (TChord V I)],Branch (NTChord I I) Prol [Branch (NTChord I I) Chord [Leaf (TChord I I)],Branch (NTChord I I) Chord [Leaf (TChord I I)]]]],Branch (NTChord I I) D5 [Branch (NTChord V I) D5 [Branch (NTChord II I) Chord [Leaf (TChord II I)],Branch (NTChord V I) Chord [Leaf (TChord V I)]],Branch (NTChord I I) Prol [Branch (NTChord I I) Chord [Leaf (TChord I I)],Branch (NTChord I I) D5 [Branch (NTChord V I) Chord [Leaf (TChord V I)],Branch (NTChord I I) Chord [Leaf (TChord I I)]]]]]]

-- >>> testTemplate
-- ProgressCancelledException

-- testTree :: Tree String
-- testTree = asTree testTemplate

plotTemplate t = toTreeDiagram' . asTree $ t

-- >>> runSearchBest $ explainEvidence  ((fmap . fmap) (`TChord` I) [[I,I]]) (NTChord I I)
-- Just (Sum {getSum = 5},WithRep (Template Prol) [New,RepLoc 1] [Template Chord])

-- parseTemplateM f x e= do
--   print "hi"
--   return $ parseAllCases f x e

data ArgMinInt a = ArgMinInt Int a deriving (Functor)

instance Semigroup (ArgMinInt a) where
  (ArgMinInt m x) <> (ArgMinInt n y) =
    if m <= n then ArgMinInt m x else ArgMinInt n y

templateParsePlot e t =
  vsep
    0
    [ text (show $ prettyEvidence e) # frame 1,
      -- text (printf "number of valid templates: %s" $ show (length templates)),
      hsep
        0
        [ vsep 1 [toTreeDiagram' $ asTree t, text (printf "cost = %d" (nRule t)) # fontSizeL 0.3],
          toTreeDiagram' $ showMaybe <$> derivedRuleTree t,
          toTreeDiagram' $ prettySymbolTree $ derivedTree (NTChord I I) t
        ]
        # centerXY,
      parseTreeOfTreeDiagram t
      -- frame 1 . text $ show $ applyTemplate (NTChord I I) bestTemplate,
      -- (text $ show bestTemplate) # fontSizeL 0.3 # frame 1
    ]
    # bg white
    # fontSizeL 0.3

main = do
  -- let testEvidence = (fmap . fmap) (`TChord` I) [[V, I]]
  let testEvidence = (fmap . fmap) (`TChord` I) [[II, V, II, V, I]]
  -- let testEvidence = [[TChord I I, TChord II (II `Of` (I `Of` I)), TChord V (II `Of` (I `Of` I)), TChord II (I `Of` I), TChord V (I `Of` I), TChord I I]]
  print testEvidence

  let templates = parseTemplate testEvidence (NTChord I I)
  print $ length templates
  -- let bestTemplate = (!! 0) templates
  -- print $ length templates
  -- let (Sum s, bestTemplate) = head $ runSearch @(Sum Int) templates

  -- let bestTemplate = minimumOn nRule templates
  -- let s = nRule bestTemplate

  -- case runSearchBest templates of
  --   Nothing -> return ()
  --   Just (s, bestTemplate) ->
  do
    let d = templateParsePlot testEvidence
    writeSVG "testTemplateAStar.svg" $ hsep 1 $ d <$> templates

-- >>> main
