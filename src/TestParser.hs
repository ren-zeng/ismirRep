{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}

module TestParser where

import CYKParser (parseCYK)
import Control.Monad.Search
import Data.Either
import Data.Foldable (minimumBy)
import Data.Functor.Foldable
import Data.List.Extra (maximumOn, minimumOn, nub, sortOn)
import Data.Monoid
import Data.Tree
import Diagrams
import Diagrams.Prelude (white)
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

explainEvidenceM e x = do
  t <- explainEvidence e x
  cost' (Sum (nRule t))
  return t

-- >>> runSearchBest $ explainEvidence  ((fmap . fmap) (`TChord` I) [[I,I]]) (NTChord I I)
-- Just (Sum {getSum = 5},WithRep (Template Prol) [New,RepLoc 1] [Template Chord])

main = do
  -- let testEvidence = (fmap . fmap) (`TChord` I) [[II, V, I, II, V, I]]
  -- let testEvidence = (fmap . fmap) (`TChord` I) [[II, II, V, I, II, V, I]]
  let testEvidence = [[TChord I I, TChord II (II `Of` (I `Of` I)), TChord V (II `Of` (I `Of` I)), TChord II (I `Of` I), TChord V (I `Of` I), TChord I I]]
  print testEvidence
  let templates = explainEvidence testEvidence (NTChord I I)
  -- print (length templates)
  let (Sum s, bestTemplate) = head $ runSearch @(Sum Int) templates

  -- let bestTemplate = minimumOn nRule templates
  --     s = nRule bestTemplate

  -- case runSearchBest templates of
  --   Nothing -> return ()
  --   Just (s, bestTemplate) ->
  do
    print bestTemplate
    let d t =
          vsep
            0
            [ text (show $ prettyEvidence testEvidence) # fontSizeL 0.3 # frame 1,
              hsep
                0
                [ vsep 1 [toTreeDiagram' $ asTree t, text (printf "cost = %d" s) # fontSizeL 0.3],
                  toTreeDiagram' $ showMaybe <$> derivedRuleTree t,
                  toTreeDiagram' $ prettySymbolTree $ derivedTree (NTChord I I) t
                ]
                # centerXY,
              parseTreeOfTreeDiagram t
              -- frame 1 . text $ show $ applyTemplate (NTChord I I) bestTemplate,
              -- (text $ show bestTemplate) # fontSizeL 0.3 # frame 1
            ]
            # bg white
    print (nRule bestTemplate)
    writeSVG "testTemplateAStar.svg" $ vsep 1 $ d <$> [bestTemplate]

-- >>> main
