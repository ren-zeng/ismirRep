{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Preliminaries.Viz where

import Data.Tree
import Diagrams
import Diagrams.Backend.SVG
import Grammar
import Meta
import TemplateGrammar
import Text.Printf (printf)

asTree :: (Show a) => Template a -> Tree String
asTree = \case
  Template x -> Node (show x) []
  Comp i x y -> Node (printf "○ %d" i) [asTree x, asTree y]
  WithRep x m ys -> Node (prettyMeta m) $ asTree x : args
    where
      args = case ys of
        [] -> []
        _ -> asTree <$> ys

prettySymbol :: Symbol Chord -> String
prettySymbol (Left (TChord x y)) = show x
prettySymbol (Right (NTChord x y)) = show x
