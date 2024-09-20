module TestParser where

import Data.Foldable (minimumBy)
import Data.List.Extra (minimumOn)
import Diagrams
import Grammar
import ParsingTemplateGrammar
import Preliminaries.TreeVisualizer (toTreeDiagram', writeSVG)
import Preliminaries.Viz
import TemplateGrammar

testTemplate =
  minimumOn nRule $
    explainEvidence
      (NTChord I I)
      [[TChord x I | x <- [I, II, V, I, V, I]]]

testTree = asTree testTemplate

main =
  writeSVG "testTemplate.svg" $
    hsep 1 $
      toTreeDiagram' <$> [testTree, prettySymbol <$> derivedTree (NTChord I I) testTemplate]

-- >>> main
