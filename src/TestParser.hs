{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications #-}

module TestParser where

import CYKParser (parseCYK)
import Control.Monad.Search
import Data.Foldable (minimumBy)
import Data.Functor.Foldable
import Data.List.Extra (minimumOn, nub, sortOn)
import Data.Monoid (Sum (getSum))
import Data.Tree
import Diagrams
import Diagrams.Prelude (white)
import Grammar
import ParsingTemplateGrammar
import Preliminaries.TreeVisualizer (toTreeDiagram', writeSVG)
import Preliminaries.Viz
import TemplateGrammar

testTemplate :: Template (ProdRule Chord)
testTemplate =
  minimumOn nRule $
    explainEvidence
      ((fmap . fmap) (`TChord` I) [[I, V, II, V, I]])
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

main = do
  let testEvidence = (fmap . fmap) (`TChord` I) [[I, III], [II], [I]]
  print testEvidence
  let templates = explainEvidence testEvidence (NTChord I I)
  print (length . nub $ derivedTree (NTChord I I) <$> templates)
  let template = minimumOn nRule templates
      d =
        vsep
          0
          [ text (show $ prettyEvidence testEvidence)
              <> (rect 3 1 # lw 0)
                # fontSizeL 1
                # bg white
                # frame 1,
            hsep
              0
              ( toTreeDiagram'
                  <$> [ asTree template,
                        showMaybe <$> derivedRuleTree template,
                        prettySymbol <$> derivedTree (NTChord I I) template
                      ]
              )
              # centerXY
          ]
          # bg white

  writeSVG "testTemplate.svg" d

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
