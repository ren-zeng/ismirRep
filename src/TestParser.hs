{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}

module TestParser where

import CYKParser (parseCYK)
import Control.Monad.Search
import Data.Foldable (minimumBy)
import Data.Functor.Foldable
import Data.List.Extra (minimumOn)
import Data.Monoid (Sum (getSum))
import Data.Tree
import Diagrams
import Grammar
import ParsingTemplateGrammar
import Preliminaries.TreeVisualizer (toTreeDiagram', writeSVG)
import Preliminaries.Viz
import TemplateGrammar
import Text.Show.Unicode

testTemplate :: Template (ProdRule Chord)
testTemplate =
  minimumOn nRule $
    explainEvidence
      ((fmap . fmap) (`TChord` I) [[I, IV, V, II, V, I]])
      (NTChord I I)

testParse = minimumOn depth . parseCYK $ fmap (`TChord` I) $ concat . replicate 3 $ [I, II, V, I, V, I]
  where
    depth = cata $ \case
      LeafF _ -> 0
      BranchF _ _ ns -> maximum ns + 1

-- >>> testParse
-- Branch (NTChord I I) RProl [Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RD5 [Branch (NTChord V I) RD5 [Branch (NTChord II I) RChord [Leaf (TChord II I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RChord [Leaf (TChord I I)]],Branch (NTChord I I) RD5 [Branch (NTChord V I) RChord [Leaf (TChord V I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RChord [Leaf (TChord I I)]]]]],Branch (NTChord I I) RProl [Branch (NTChord I I) RProl [Branch (NTChord I I) RD5 [Branch (NTChord V I) RD5 [Branch (NTChord II I) RChord [Leaf (TChord II I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RChord [Leaf (TChord I I)]],Branch (NTChord I I) RD5 [Branch (NTChord V I) RChord [Leaf (TChord V I)],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RChord [Leaf (TChord I I)]]]],Branch (NTChord I I) RD5 [Branch (NTChord V I) RD5 [Branch (NTChord II I) RChord [Leaf (TChord II I)],Branch (NTChord V I) RChord [Leaf (TChord V I)]],Branch (NTChord I I) RProl [Branch (NTChord I I) RChord [Leaf (TChord I I)],Branch (NTChord I I) RD5 [Branch (NTChord V I) RChord [Leaf (TChord V I)],Branch (NTChord I I) RChord [Leaf (TChord I I)]]]]]]

-- >>> testTemplate
-- ProgressCancelledException

-- testTree :: Tree String
-- testTree = asTree testTemplate

main =
  writeSVG "testTemplate.svg" $
    hsep 1 $
      toTreeDiagram' <$> [asTree testTemplate, showMaybe <$> derivedRuleTree testTemplate, prettySymbol <$> derivedTree (NTChord I I) testTemplate]

-- main =
--   writeSVG "testCYK.svg" $
--     hsep 1 $
--       toTreeDiagram' <$> [prettySymbol <$> valTree testParse]

showMaybe :: (Show a) => Maybe a -> String
showMaybe = \case
  Just x -> show x
  Nothing -> "●"

-- ProgressCancelledException
-- >>> main
