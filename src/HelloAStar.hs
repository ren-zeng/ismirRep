{-# LANGUAGE FlexibleContexts #-}

module HelloAStar where

import Control.Applicative
import Control.Monad
import Control.Monad.Search
import Data.Maybe
import Data.Monoid

type Location = (Int, Int)

type Distance = Sum Int

distance :: Location -> Location -> Distance
distance (x, y) (x', y') = abs (Sum x' - Sum x) + abs (Sum y' - Sum y)

neighbors :: Location -> [(Location, Distance)]
neighbors (x, y) = [((x + i, y + j), abs (Sum i) + abs (Sum j)) | i <- [-1, 0, 1], j <- [-1, 0, 1], abs (Sum i) + abs (Sum j) == 1]

shortestRoute :: (Location -> Bool) -> (Location -> Sum Int) -> Location -> Maybe (Distance, [Location])
shortestRoute hasTreasure estDistance from = runSearchBest $ go [from]
  where
    go ls =
      if hasTreasure (head ls)
        then return ls
        else msum $ (\(l, d) -> cost' d >> go (l : ls)) <$> neighbors (head ls)

-- >>> shortestRoute (0,0) (10,10)

-- All naturals, weighted by the size of the number
naturals :: Search (Sum Integer) Integer
naturals = return 0 <|> (cost' (Sum 1) >> ((+ 1) <$> naturals))

-- [ 0, 1, 2, 3, 4, 5, ... ]

-- All pairs of naturals
pairs :: Search (Sum Integer) (Integer, Integer)
pairs = do
  x <- naturals
  y <- naturals
  return (x, y)

--    [ (0, 0), (1, 0), (0, 1), (1, 1), (2, 0), ... ]
-- or [ (0, 0), (0, 1), (1, 0), (2, 0), (1, 1), ... ]
-- or ...

-- >>> take 100 $ runSearch pairs
-- [(Sum {getSum = 0},(0,0)),(Sum {getSum = 1},(1,0)),(Sum {getSum = 1},(0,1)),(Sum {getSum = 2},(2,0)),(Sum {getSum = 2},(1,1)),(Sum {getSum = 2},(0,2)),(Sum {getSum = 3},(3,0)),(Sum {getSum = 3},(2,1)),(Sum {getSum = 3},(1,2)),(Sum {getSum = 3},(0,3)),(Sum {getSum = 4},(4,0)),(Sum {getSum = 4},(3,1)),(Sum {getSum = 4},(2,2)),(Sum {getSum = 4},(1,3)),(Sum {getSum = 4},(0,4)),(Sum {getSum = 5},(5,0)),(Sum {getSum = 5},(4,1)),(Sum {getSum = 5},(3,2)),(Sum {getSum = 5},(2,3)),(Sum {getSum = 5},(1,4)),(Sum {getSum = 5},(0,5)),(Sum {getSum = 6},(6,0)),(Sum {getSum = 6},(5,1)),(Sum {getSum = 6},(4,2)),(Sum {getSum = 6},(3,3)),(Sum {getSum = 6},(2,4)),(Sum {getSum = 6},(1,5)),(Sum {getSum = 6},(0,6)),(Sum {getSum = 7},(7,0)),(Sum {getSum = 7},(6,1)),(Sum {getSum = 7},(5,2)),(Sum {getSum = 7},(4,3)),(Sum {getSum = 7},(3,4)),(Sum {getSum = 7},(2,5)),(Sum {getSum = 7},(1,6)),(Sum {getSum = 7},(0,7)),(Sum {getSum = 8},(8,0)),(Sum {getSum = 8},(7,1)),(Sum {getSum = 8},(6,2)),(Sum {getSum = 8},(5,3)),(Sum {getSum = 8},(4,4)),(Sum {getSum = 8},(3,5)),(Sum {getSum = 8},(2,6)),(Sum {getSum = 8},(1,7)),(Sum {getSum = 8},(0,8)),(Sum {getSum = 9},(9,0)),(Sum {getSum = 9},(8,1)),(Sum {getSum = 9},(7,2)),(Sum {getSum = 9},(6,3)),(Sum {getSum = 9},(5,4)),(Sum {getSum = 9},(4,5)),(Sum {getSum = 9},(3,6)),(Sum {getSum = 9},(2,7)),(Sum {getSum = 9},(1,8)),(Sum {getSum = 9},(0,9)),(Sum {getSum = 10},(10,0)),(Sum {getSum = 10},(9,1)),(Sum {getSum = 10},(8,2)),(Sum {getSum = 10},(7,3)),(Sum {getSum = 10},(6,4)),(Sum {getSum = 10},(5,5)),(Sum {getSum = 10},(4,6)),(Sum {getSum = 10},(3,7)),(Sum {getSum = 10},(2,8)),(Sum {getSum = 10},(1,9)),(Sum {getSum = 10},(0,10)),(Sum {getSum = 11},(11,0)),(Sum {getSum = 11},(10,1)),(Sum {getSum = 11},(9,2)),(Sum {getSum = 11},(8,3)),(Sum {getSum = 11},(7,4)),(Sum {getSum = 11},(6,5)),(Sum {getSum = 11},(5,6)),(Sum {getSum = 11},(4,7)),(Sum {getSum = 11},(3,8)),(Sum {getSum = 11},(2,9)),(Sum {getSum = 11},(1,10)),(Sum {getSum = 11},(0,11)),(Sum {getSum = 12},(12,0)),(Sum {getSum = 12},(11,1)),(Sum {getSum = 12},(10,2)),(Sum {getSum = 12},(9,3)),(Sum {getSum = 12},(8,4)),(Sum {getSum = 12},(7,5)),(Sum {getSum = 12},(6,6)),(Sum {getSum = 12},(5,7)),(Sum {getSum = 12},(4,8)),(Sum {getSum = 12},(3,9)),(Sum {getSum = 12},(2,10)),(Sum {getSum = 12},(1,11)),(Sum {getSum = 12},(0,12)),(Sum {getSum = 13},(13,0)),(Sum {getSum = 13},(12,1)),(Sum {getSum = 13},(11,2)),(Sum {getSum = 13},(10,3)),(Sum {getSum = 13},(9,4)),(Sum {getSum = 13},(8,5)),(Sum {getSum = 13},(7,6)),(Sum {getSum = 13},(6,7)),(Sum {getSum = 13},(5,8))]
