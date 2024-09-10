{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
import Data.Tree

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

newtype CachedF k f b = CachedF (k || f b) deriving (Functor)

type Cached k a = Fix (CachedF k (Base a))

data SLG k f a = SLG
  { start :: f (Cached k a),
    bindings :: Map k (Cached k a)
  }

decompressL :: (Corecursive a, Ord k) => SLG k Identity a -> a
decompressL = runIdentity . decompressG

decompressG :: (Corecursive a, Ord k, Functor f) => SLG k f a -> f a
decompressG slg = substitute (bindings slg Map.!) <$> start slg

data SLGEncoder k f a = SLGEncoding
  { encodeSLG :: f a -> SLG k f a,
    decodeSLG :: SLG k f a -> f a
  }

testForestSLG :: SLG k [] (Tree a)
testForestSLG = undefined
