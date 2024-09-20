{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module SLG where

import Data.Bifunctor (Bifunctor)
import Data.Fix hiding (cata)
import Data.Foldable
import Data.Function
import Data.Functor.Base
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.Kind
import Data.Map
import qualified Data.Map as Map
import Data.MemoTrie
import qualified Data.Set as Set
import Data.Tree
import Meta
import TemplateGrammar

class Cachable k a where
  type C k a
  substitute :: (k -> C k a) -> C k a -> a

instance (Corecursive a) => Cachable k a where
  type C k a = Cached k a
  substitute f = cata alg
    where
      alg :: CachedF k (Base a) a -> a
      alg (CachedF e) = either (substitute f . f) embed e

type (||) = Either

newtype CachedF k f b = CachedF (Either k (f b)) deriving (Functor)

type Cached k a = (Fix (CachedF k (Base a)))

data SLG k f a = SLG
  { start :: f (Cached k a),
    bindings :: Map k (Cached k a)
  }

pattern CacheVal x = Fix (CachedF (Right x))

pattern CacheVar x = Fix (CachedF (Left x))

decode :: (Corecursive a, Ord k) => SLG k Identity a -> a
decode = runIdentity . decodeF

decodeF :: (Corecursive a, Ord k, Functor f) => SLG k f a -> f a
decodeF slg = substitute (bindings slg Map.!) <$> start slg

data SLGEncoder k f a = SLGEncoder
  { encodeSLG :: f a -> SLG k f a
  }

pattern NodeC x y = CacheVal (NodeF x y)

testForestSLG :: SLG String Identity (Tree Int)
testForestSLG =
  SLG
    { start = Identity $ NodeC 2 [NodeC 3 [CacheVar "a", CacheVar "b"]],
      bindings = fromList [("a", NodeC 999 []), ("b", NodeC 100 [CacheVar "a", CacheVar "a"])]
    }

-- >>> decode testForestSLG
-- Node {rootLabel = 2, subForest = [Node {rootLabel = 3, subForest = [Node {rootLabel = 999, subForest = []},Node {rootLabel = 100, subForest = [Node {rootLabel = 999, subForest = []},Node {rootLabel = 999, subForest = []}]}]}]}

isLeaf :: Tree a -> Bool
isLeaf (Node _ []) = True
isLeaf _ = False

allDepth1Tree :: (Ord a) => Tree a -> Set.Set (Tree a)
allDepth1Tree (Node x []) = mempty
allDepth1Tree t
  | all isLeaf (subForest t) = Set.singleton t
  | otherwise = Set.unions (allDepth1Tree <$> subForest t)

-- dedupTree' :: (Ord a) => SLG k Identity (Tree a) -> SLG k Identity (Tree a)
-- dedupTree' (SLG (Identity s) b) = SLG (Identity s') b' where
--   toCache = allDepth1 s
--   s' = undefined
--   b' = undefined

dedupTree = hoistFix (\(NodeF x []) -> (NodeF x []))

-- >>>  Node 1 [Node 2 [Node 10 [] ,Node 12 []], Node 3 [ Node 2 [], Node 2 []]]
-- Node {rootLabel = 1, subForest = [Node {rootLabel = 2, subForest = [Node {rootLabel = 10, subForest = []},Node {rootLabel = 12, subForest = []}]},Node {rootLabel = 3, subForest = [Node {rootLabel = 2, subForest = []},Node {rootLabel = 2, subForest = []}]}]}

encodeTree :: Identity (Tree a) -> SLG String Identity (Tree a)
encodeTree (Identity t) = SLG (Identity s) b
  where
    (s, b) = case t of
      Node x [] -> (NodeC x [], mempty)
      Node x ts -> undefined

pattern TemplateC x = CacheVal (TemplateF x)

pattern CompC i x y = CacheVal (CompF i x y)

pattern WithRepC x m ys = CacheVal (WithRepF x m ys)

testTemplateSLG :: SLG String Identity (Template Int)
testTemplateSLG =
  SLG
    { start = Identity $ WithRepC (TemplateC 2) [Star, New] [CacheVar "b"],
      bindings = fromList [("a", CompC 1 (TemplateC 10) (TemplateC 100)), ("b", CompC 2 (CacheVar "a") (CacheVar "a"))]
    }

-- >>> decode testTemplateSLG
-- WithRep (Template 2) [Star,New] [Comp 2 (Comp 1 (Template 10) (Template 100)) (Comp 1 (Template 10) (Template 100))]
