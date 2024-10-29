{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Meta where

import Data.List
import Data.MemoTrie
import GHC.Generics (Generic)
import Text.Printf

data RepSymbol = New | RepLoc Int | Star deriving (Show, Eq, Ord, Generic)

instance HasTrie RepSymbol where
  newtype RepSymbol :->: b = RepSymbolTrie {unRepSymbolTrie :: Reg RepSymbol :->: b}
  trie = trieGeneric RepSymbolTrie
  untrie = untrieGeneric unRepSymbolTrie
  enumerate = enumerateGeneric unRepSymbolTrie

type Meta = [RepSymbol]

useMeta' :: Meta -> a -> [a] -> [a] -> [a]
useMeta' [] _ _ done = done
useMeta' (m : ms) r xs done = case m of
  New -> useMeta' ms r (tail xs) (done ++ [head xs])
  Star -> useMeta' ms r xs (done ++ [r])
  RepLoc i -> useMeta' ms r xs (done ++ [done !! (i - 1)])

useMeta :: Meta -> a -> [a] -> [a]
useMeta ms r xs = useMeta' ms r xs []

-- >>> useMeta [New,RepLoc 1,New,Star,RepLoc 3] 999 [50,8]
-- [50,50,8,999,8]

simplifyByMeta :: Meta -> [a] -> [a]
simplifyByMeta m xs = [x | (s, x) <- zip m xs, s == New]

freeVar :: Meta -> Int
freeVar = foldr (\x -> if x == New then (+ 1) else id) 0

prettyMeta :: Meta -> String
prettyMeta m = printf "⟨ %s ⟩" . unwords $ (go <$> m)
  where
    go New = "_"
    go Star = "★"
    go (RepLoc i) = printf "%d" i

inferMetaAcc :: (Eq b) => b -> [b] -> [b] -> Meta
inferMetaAcc r seen [] = []
inferMetaAcc r seen (x : xs) = y : inferMetaAcc r (seen ++ [x]) xs
  where
    y = if x == r then Star else maybe New (RepLoc . (1 +)) (elemIndex x seen)

inferMeta' :: (Eq a) => a -> [a] -> Meta
inferMeta' r = inferMetaAcc r []

inferMeta :: (Eq a) => a -> [a] -> (Meta, [a])
inferMeta x xs = (m, simplifyByMeta m xs) where m = inferMeta' x xs

-- >>> inferMeta 99 [1,1,3,3,99]
-- ([New,RepLoc 1,New,RepLoc 3,Star],[1,3])
