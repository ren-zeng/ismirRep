{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Meta where

import Text.Printf

data RepSymbol = New | RepLoc Int | Star deriving (Show, Eq, Ord)

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
