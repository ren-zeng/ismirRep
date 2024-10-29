{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Preliminaries.Viz where

import Data.Functor.Foldable
import Data.List (intersperse)
import Data.List.Extra
import Data.Maybe
import Data.Tree
import Diagrams
import Diagrams.Backend.SVG
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree (renderTree, slHSep, slHeight, slVSep, slWidth, symmLayout, symmLayout')
import GrammarInstances
import Meta
import Preliminaries.Grammar
import Preliminaries.TreeVisualizer (closer, parseTreeDiagram, toTreeDiagram', treeDiagram')
import TemplateGrammar
import Text.Printf (printf)

asTree :: (Show a) => Template a -> Tree String
asTree = \case
  Template x -> Node (show x) []
  Id -> Node ("Id") []
  WithRep x m ys -> Node (prettyMeta m) $ asTree x : args
    where
      args = case ys of
        [] -> []
        _ -> asTree <$> ys

showMaybe :: (Show a) => Maybe a -> String
showMaybe = \case
  Just x -> show x
  Nothing -> "●"

prettySymbolTree :: Tree (Symbol Chord) -> Tree String
prettySymbolTree (Node x ts) = Node (prettySymbol x ++ downArrow) (prettySymbolTree <$> ts)
  where
    downArrow = case (x, ts) of
      (Right _, []) -> "↓"
      _ -> mempty

asTreeOfTree :: (Grammar a) => Template (ProdRule a) -> Tree (Tree String)
asTreeOfTree = \case
  Template x -> Node ((fmap showMaybe . derivedRuleTree) (Template x)) []
  Id -> Node (Node "Id" []) []
  WithRep t m ts ->
    Node
      ((fmap showMaybe . derivedRuleTree) (WithRep t m ts))
      (asTreeOfTree <$> t : ts)

-- >>> asTreeOfTree $  (WithRep (Template D5) [Star,New] [Template Chord])
-- Node {rootLabel = Node {rootLabel = "D5", subForest = [Node {rootLabel = "D5", subForest = [Node {rootLabel = "\9679", subForest = []},Node {rootLabel = "\9679", subForest = []}]},Node {rootLabel = "Chord", subForest = []}]}, subForest = [Node {rootLabel = Node {rootLabel = "Chord", subForest = []}, subForest = []}]}

asParseTreeOfTree :: (Grammar a) => Template (ProdRule a) -> ParseTree (Tree String) Meta (Tree String)
asParseTreeOfTree = \case
  Template x -> Leaf ((fmap showMaybe . derivedRuleTree) (Template x))
  Id -> Leaf (Node "●" [Node "●" []])
  WithRep t m ts ->
    Branch
      ((fmap showMaybe . derivedRuleTree) (WithRep t m ts))
      m
      (asParseTreeOfTree <$> t : ts)

prettySymbol :: Symbol Chord -> String
prettySymbol (Left (TChord x y)) =
  if simplifyNumeral y == I
    then printf "%s" (show x)
    else printf "%s/%s" (show x) (show $ simplifyNumeral y)
prettySymbol (Right (NTChord x y)) =
  if simplifyNumeral y == I
    then printf "%s" (show x)
    else printf "%s/%s" (show x) (show $ simplifyNumeral y)

prettyEvidence :: [[T Chord]] -> String
prettyEvidence e = intercalate " __ " (fmap (unwords . fmap (prettySymbol . Left)) e)

treeOfTreeDiagram t =
  renderTree
    id
    (closer 0.1 (~~) # lwL 0.025) -- # lw 0.25
    ( symmLayout'
        ( with
            & slHSep
              .~ 1
            & slVSep
              .~ 1
            & slWidth
              .~ fromMaybe (0, 0)
                . extentX
            & slHeight
              .~ fromMaybe (0, 0)
                . extentY
        )
        (toTreeDiagram' <$> t)
    )
    # centerXY
    # frame 1
    # bg white

parseTreeOfTreeDiagram :: (Grammar a) => Template (ProdRule a) -> Diagram B
parseTreeOfTreeDiagram t =
  parseTreeDiagram
    toTreeDiagram'
    (text . prettyMeta)
    (asParseTreeOfTree t)
    # frame 1
