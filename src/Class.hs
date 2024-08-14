{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies,ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Class where
import Control.Monad.Bayes.Class
import Data.Kind
import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))
import Grammar
import Data.Tree
import qualified Data.Vector  as Vector hiding (mapM)
import Control.Monad.Bayes.Sampler.Lazy (weightedSamples)
import Control.Monad.Bayes.Sampler.Strict
import Control.Monad.Bayes.Inference.Lazy.WIS (lwis)
import Text.Printf
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced hiding (model)

import System.Random.Stateful hiding (uniform)
import System.Random.Internal
import Control.Monad
import Control.Monad.Bayes.Enumerator (toEmpirical)
import Data.Vector hiding (mapM)



type (+) = Either

{-|
This concept has been formalize as Lens combined with Para
-}

-- type family a ⨂ b where
--     () ⨂ () = ()
--     a ⨂ () = a 
--     () ⨂ a = a
--     a ⨂ b = Pair a b



type (⨂) = (,)
type (⨁) = Either


data FreeParam a z b where
    FreeA :: (a -> z -> b) -> FreeParam a z b
    SeqA :: FreeParam a z b -> FreeParam b z' c -> FreeParam a (z ⨂ z') c
    ProductA :: FreeParam a z b -> FreeParam a' z' b' -> FreeParam (a ⨂ a') (z ⨂ z') (b ⨂ b')
    SumA :: FreeParam a z b -> FreeParam a' z' b' -> FreeParam (a ⨁ a') (z ⨁ z') (b ⨁ b')




free1 = FreeA (\x () -> x)

free2 = FreeA (\x y -> (x,x,y))

dup = FreeA (\x () -> (x,x))

free3 = free1 `SeqA` free2

free4 = (ProductA free1 free2)

class ParamArrow f  where
    arrP :: (a -> z -> b) -> f a z b
    (->-)  :: f a () a
    (>->)  :: f a z b -> f b z' c -> f a (z ⨂ z') c
    (~~>)  :: f a z z' -> f a' z' b -> f (a ⨂ a') z b
    (=*=)  :: f a z b -> f a' z' b' -> f (a ⨂ a') (z ⨂ z') (b ⨂ b')
    (=+=)  :: f a z b -> f a' z' b -> f (a + a') (z + z') (b + b)

splitArr a = a >-> arrP (\x () -> (x,x))

-- class TwoWayStoch m f where
--     forwardF  :: f a (m b)
--     backwardF :: f b (m a)



data BayesianNet m a z b = BayesianNet {
    forward  :: (a ⨂ z) -> m b,
    backward :: b -> m (a ⨂ z)
}


-- P(a,z |b)
-- P(z | b, a=1)

{-  
    model :: (m b, p (a,b))
    a<-D
    b<-D'(A)
    return b
    
    p (a,b) = p a * p (b|a)
    
    we have m (a,b), free to condition on a or b

    goal : flexibly fix any variable in the program
    - choice1 : p(a,b) -> p(b|a=_)
    - choice2 : p(a,b) -> p(a|b=b0) for example filtering out runs whose outcome that is not b0

    1. write model once (semantics is only about the joint distribution)
    2. (query) custimizable conditioning
    3. being able to resample from a given point in a run
        - what if things happend differently at this particular point in the timeline?

    core difficulty: type signature of the trace

    bernulli :: double -> bool
    bernulli':: bool -> double

    need (bernulli' >>> bernulli == id)
-}


data Model m a z b = Model {
    priorM :: m (a ⨂ z),
    generate :: (a ⨂ z) -> m b,
    prob :: (a ⨂ z) -> b -> Log Double
    }



idModel :: (Monad m) => m a -> Model m a () a
idModel ma = Model ((,()) <$> ma) (return . fst) (\_ _ -> 0)

idBayesian :: (Monad m) => BayesianNet m a () a
idBayesian = BayesianNet {
    forward = return. fst ,
    backward =  \z -> return (z,())
}


toBaysianNet :: MonadFactor m => Model m a z b -> BayesianNet m a z b
toBaysianNet (Model priorM generate p) = BayesianNet {
    forward = generate,
    backward = \b -> do
        inputs <- priorM
        factor (p inputs b)
        return inputs
}

instance (Monad m) => ParamArrow (BayesianNet m) where
    (->-) = BayesianNet {
        forward   = \(a,()) -> return a,
        backward  = \b -> return (b,())
    }


    f >-> g = BayesianNet {
        forward = \(a,(z1,z2)) -> do
            b <- forward f (a,z1)
            forward g (b,z2),
        backward = \c -> do
            (b,z2) <- backward g c
            (a,z1) <- backward f b
            return (a,(z1,z2))
    }

    f ~~> g = BayesianNet {
        forward = \((a,a'),z) -> do
            z' <- forward f (a,z)
            forward g (a',z'),
        backward = \b -> do
            (a',z') <- backward g b
            (a ,z ) <- backward f z'
            return ((a,a'),z)
    }

    f =*= g = BayesianNet {
        forward = \((a,a'),(z,z')) -> liftA2 (,) (forward f (a,z)) (forward g (a',z')),
        backward = \(b,b') -> do
            (a,z) <- backward f b
            (a',z') <- backward g b'
            return ((a,a'),(z,z'))
    }

    f =+= g = BayesianNet {
        forward = \case
                (Left a,Left z)  ->  Left <$> forward f (a,z)
                (Right a',Right z') -> Right <$> forward g (a',z'),
        backward = \case
            Left b -> do
                (a,z) <- backward f b
                return (Left a,Left z)
            Right b -> do
                (a',z') <- backward g b
                return (Right a', Right z')
    }

linearModel :: MonadMeasure m => BayesianNet m Double (Double, Double) Double
linearModel = BayesianNet {
    forward = \(a,(slope,noise)) -> do
        return $ slope * a + noise,

    backward = \b -> do
        a <- uniform 0 10
        slope <- normal 0 1
        noise <- normal 1 1
        factor $ normalPdf (slope * a) (sqrt noise) b
        return (a,(slope, noise))
}


modelTest () =  (linearModel =*= linearModel) ~~> linearModel


anaMTree :: Monad m => (a -> m [a]) -> a -> m (Tree a)
anaMTree f x = do
    xs <- f x
    trees <- mapM (anaMTree f) xs
    return $ Node x trees

anaMTreeInfer :: Monad m => Tree a -> m (a -> m [a], a)
anaMTreeInfer = undefined




type BN =  BayesianNet

growTreeModel :: (MonadMeasure m) => BN m (BN m a () [a]) a (Tree a)
growTreeModel = BayesianNet {
    forward = \(net,seed) -> do
        children <- forward net (seed,())
        subtrees <- mapM (\x -> forward growTreeModel (net,x)) children
        return $ Node seed subtrees,

    backward = \t -> undefined
}

--elaboratorModel :: (MonadMeasure m) => BayesianNet m a () [a]

elaboratorModel :: MonadMeasure m => BayesianNet m b ((() ⨂ ()) ⨂ ()) [b]
elaboratorModel = splitArr (->-) >-> (ruleWeightModel ~~> ruleAppModel)

ruleWeightModel :: BayesianNet m a () [Double]
ruleWeightModel = undefined

ruleAppModel :: MonadMeasure m => BayesianNet m a [Double] [a]
ruleAppModel = undefined



r :: _ => BayesianNet  m () () (BayesianNet m b ((() ⨂ ()) ⨂ ()) [b])
r = BayesianNet {forward = \(_,_) -> return elaboratorModel, backward = \_ -> return ((),())}


