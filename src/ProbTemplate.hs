module ProbTemplate where

import Control.Applicative
import Data.Either
import Grammar
import TemplateGrammar

sampleTemplate ::
  (Monad m, Alternative m, Grammar a) =>
  (NT a -> Int -> m (ProdRule a)) ->
  m Int ->
  (Int -> m Meta) ->
  ([Int] -> m Int) ->
  NT a ->
  Int ->
  m (Template (ProdRule a))
sampleTemplate rulePrior arityPrior metaPrior categoricalPrior x 0 =
  let go =
        sampleTemplate
          rulePrior
          arityPrior
          metaPrior
          categoricalPrior
   in (Template <$> rulePrior x 0)
        <|> do
          n <- arityPrior
          t1 <- go x n
          i <- categoricalPrior $ filter (\k -> isRight (argTypes t1 !! k)) [0 .. n]
          let Right nt = argTypes t1 !! i
          t2 <- go nt 0
          return $ Comp i t1 t2
        <|> do
          n <- arityPrior
          t1 <- go x n
          m <- metaPrior n
          let xs = rights $ freeArgs m (argTypes t1)
          ts <- mapM (`go` 0) xs
          return $ WithRep t1 m ts

-- pcfg :: (Monad m, Grammar a)
--     => (NT a -> m (ProdRule a))
--     -> NT a
--     -> m [T a]
