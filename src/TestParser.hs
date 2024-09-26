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
import Data.Monoid (Sum (getSum))
import Data.Tree
import Diagrams
import Diagrams.Prelude (white)
import Grammar
import Meta
import ParsingTemplateGrammar
import Preliminaries.TreeVisualizer (toTreeDiagram', treeDiagram', writeSVG)
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

plotTemplate t = toTreeDiagram' . asTree $ t

main = do
  -- let testEvidence = (fmap . fmap) (`TChord` I) [[IV, V, I, IV, V, I]]
  let testEvidence = [[TChord I I, TChord II (II `Of` (I `Of` I)), TChord V (II `Of` (I `Of` I)), TChord II (I `Of` I), TChord V (I `Of` I), TChord I I]]
  print testEvidence
  let templates = explainEvidence testEvidence (NTChord I I)
  print (length templates)
  let bestTemplate = (!! 0) $ (sortOn nRule) templates
  let d t =
        vsep
          0
          [ text (show $ prettyEvidence testEvidence) # fontSizeL 0.3 # frame 1,
            hsep
              0
              ( toTreeDiagram'
                  <$> [ asTree t,
                        showMaybe <$> derivedRuleTree t,
                        prettySymbolTree $ derivedTree (NTChord I I) t
                      ]
              )
              # centerXY,
            parseTreeOfTreeDiagram t
          ]
          # bg white
  print (nRule bestTemplate)
  writeSVG "testTemplate.svg" $ vsep 1 $ d <$> [bestTemplate]

-- >>> main
