{-# LANGUAGE AllowAmbiguousTypes,Arrows #-}
{-# LANGUAGE PartialTypeSignatures,ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}


module BayesianLens where
import Control.Monad.Bayes.Class
import Data.Vector (fromList, toList)
import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))
import Control.Monad

import Control.Monad.Bayes.Enumerator (enumerate, enumerator, explicit)
import Grammar
import Data.List.Extra ((!?))
import Control.Monad.Fix
import Data.Either.Extra (maybeToEither, fromLeft)
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT), mapMaybeT, hoistMaybe)
import Data.Functor.Identity (Identity)
import Control.Monad.Trans.Class (MonadTrans)
import Data.Bits (Bits(xor))
import Control.Monad.Bayes.Inference.Lazy.MH (mh)
import Control.Monad.Bayes.Weighted (runWeightedT)
import Data.Maybe (fromJust)
import Data.Tree
import qualified Control.Monad.Bayes.Inference.Lazy.MH as Lazy
import Data.List





-- data Lens a a' b b' where
--     Lens :: (a -> (a,b))  ->  ((a,b') -> a')  -> Lens a a' b b'


-- connect :: Lens a a' b b' -> Lens b b' c c' -> Lens a a' c c'
-- (Lens forwF backF) `connect` (Lens forwG backG) = Lens forw back where 
--     forw x = ((c1,c2),y2) where 
--         (c1,y1) = forwF x
--         (c2,y2) = forwG y1
--     back ((c1,c2),y) = x1 where 
--         x2 = backG (c2,y)
--         x1 = backF (c1,x2)




-- type BaysianLens m a b =  (Lens (m a) (m a) (m b) b) 

-- -- pattern Forward x <- (BaysianOptic x _) where 
-- --     Forward x   (BaysianOptic x _)

-- (->-) :: forall m a b c. BaysianOptic m a b -> BaysianOptic m b c -> BaysianOptic m a c
-- BaysianOptic (Optic goF backF) ->- BaysianOptic (Optic goG backG) = BaysianOptic (Optic go back) where 
--     go x = do 
--         (a1,y1) <- goF x
--         (a2,y2) <- goG y1
--         return ((a1,a2),y2)




-- instance Monad m => Category (BaysianOptic m) where 
--     id = undefined

-- -- instance Category (BaysianOptic m) where 
-- --     (.)  =  liftA2 $ flip connect 


-- deterministic :: Monad m => (a -> b) -> BaysianOptic m a b
-- deterministic f = BaysianOptic $ Optic ((,) <$> return <*> return . f) fst


-- catChoice :: (MonadDistribution m) => BaysianOptic m [Double] Int
-- catChoice = BaysianOptic $ Optic 
--     (\x -> (return x, categorical (fromList x)))
--     (\(pri, n) -> do 
--         w <- pri 
--         return ((\(i,x) -> if i==n then x+1 else x) <$> zip [0..] w)
--     )



{-
Bayesian Lenses from 
The Compositional Structure of Bayesian Inference
* Dylan Braithwaite 
* Jules Hedges
* Toby St Clere Smithe

   f     g
X --> Y --> Z
A <-- B <-- C
   f#    g#

-}

data BayesChannel m a b = BayesChannel {
    forw :: a -> m b,       -- markov kernel from a to b
    back :: m a -> b -> m a -- posterior update given an observation
}



type a <=> b = forall m. (MonadMeasure m) => BayesChannel m a b
type a ⥂ b = a <=> b

instance (Monad m) => Category (BayesChannel m) where

    id = BayesChannel {
        forw = return,
        back = const return
    }

    BayesChannel g g'  . BayesChannel f f'  = BayesChannel {
        forw = f >=> g, -- kleisli composition
        back = \ma  -> g' (f =<< ma) >=> f' ma -- chain rule of bayesian inverse | analogous to chain rule in calculus D (g.f) x = D g (g.f $ x) (D f x)
    }

fromFunc :: Eq b => (a -> b) -> a ⥂ b
fromFunc f = BayesChannel {
        forw = return . f,
        back = \ma y -> do
            a <- ma
            condition (y == f a) -- score a by 0 | if `f x /= y`  then  `p (x|y) = 0`.
            return a
    }

instance (Monad m) => Arrow (BayesChannel m) where

    arr f = error "BayesChannel for arbitrary function is not defined"

    -- | Product of `BayesChannel` represents (parralel markov kernel, parralel inference)    
    BayesChannel f f'  *** BayesChannel g g'  = BayesChannel {
        forw = \(x1,x2) -> (,) <$> f x1 <*> g x2,
        back = \ma (y1,y2) -> let (ma1,ma2) = (fmap fst &&& fmap snd) ma in
            (,) <$> f' ma1 y1 <*> g' ma2 y2
    }

{-
f :: a -> m b
f' :: m a -> b -> m a
need :: m (m' a) -> m' b -> m (m' a)
-}
class (Arrow ar, Monad m) => MFunctor ar m where 
  mMap :: ar a b -> ar (m a) (m b)

goal :: (MFunctor to m) => (a `to` m b) -> (b `to` m c) -> (a `to` m c) 
goal f g = f >>> mMap g >>> arr join 

instance (Monad m, Monad m', Traversable m') => MFunctor (BayesChannel m) m' where 
    mMap :: BayesChannel m a b -> BayesChannel m (m' a) (m' b)
    mMap (BayesChannel f f') = BayesChannel {
    forw = mapM f,
    back = \mm'a mb -> do
        m'a <- mm'a
        
        undefined
}

instance (Monad m) => MFunctor (BayesChannel m) Maybe where 
    mMap (BayesChannel f f') = BayesChannel {
        forw = mapM f,
        back = \mm'a mb -> do 
            m'a <- mm'a
            let c = sequence (f <$> m'a)
                d = f' 
            undefined
    }


mapA :: (Traversable m', Traversable m, Monad m, Monad m') => BayesChannel m a b -> BayesChannel m (m' a) (m' b)
mapA (BayesChannel f f') = BayesChannel {
    forw = mapM f,
    back = \mas bs -> do
        let c = f' <$> sequence mas <*> bs
        sequence c
}


dup :: Eq a => a ⥂ (a,a)
dup = fromFunc (\x-> (x,x))


instance (Monad m) => ArrowChoice (BayesChannel m) where

    -- | Sum of `BayesChannel m` represents either channel1 or channel2
    BayesChannel f f' +++ BayesChannel g g' = BayesChannel {
        forw = \case
            Left x1 -> Left <$> f x1
            Right x2 -> Right <$> g x2,
        back = \ma b -> do
            a <- ma
            case (a,b) of
                (Left x, Left y) -> Left <$> f' (pure x) y
                (Right x, Right y) -> Right <$> g' (pure x) y
                _ -> error "unexpected case in Either channel"
    }


-- instance (MonadMeasure m, MonadFix m) => ArrowLoop (BayesChannel m) where
--   loop (BayesChannel f f') = BayesChannel {
--     forw = \b -> do 
--         rec (c,d) <- f (b,d)
--         return c,
--     back = \ma y -> do 
--         a <- ma 
--         b <- forw a
--         condition (f a == y) 
--         return a
--   } 


{- | `kChannel` is the BayesianLens for categorical distribution. 
forward markov kernel :: maps the parameter alphas in the dirichlet prior to integer representing a choice among k options.
inference :: prior -> observed choice -> posterior
-}
kChannel :: [Double] ⥂ Int
kChannel = BayesChannel {
    forw = \x -> do
        i <- categorical $ fromList x
        score (toLog $ x !! i )
        return i,
    back = \ma y -> do
        a <- ma
        case a !? y of
            Nothing -> condition False
            Just x -> score $ toLog (x/sum a)-- multiply by the probability of obtaining index y, which is the normalized yth weight in categorical distribution
        return a
}




{-|
`unfoldMChannel`
curly bracket indicates deterministic channel created by `fromFunc`
non-bracket (like kChannel) indicates stochastic channel

    NT a                       Maybe [Symbol a]
------>----- (   ? ?   ) ----------->----
            |           |                            
             ----->-----      

-}

unfoldM f x = case f x of
    Nothing -> Just [x]
    Just xs -> foldMap (unfoldM f) xs

--unfoldMChannel :: (MonadMeasure m) => (a -> b) -> BayesChannel m (a -> b, a) b
unfoldMChannel :: _ =>  BayesChannel m (NT a) (Maybe [Symbol a])
unfoldMChannel = loop (first elabChannel)





-- | this is like (>=>) but paramatrized by an addition layer of monad
(>>=>) :: (Monad m, BayesKleisliComposable m') => BayesChannel m a (m' b) -> BayesChannel m b (m' c) -> BayesChannel m a (m' c)
(BayesChannel f f') >>=> (BayesChannel g g') = BayesChannel {
    forw = \a -> do
        m'b <- f a
        ingredient1 g m'b,
    back = \ma -> backM g' (f =<< ma) >=> f' ma
}



backM :: (Monad m, BayesKleisliComposable m') => (m a -> m' b -> m a) -> (m (m' a) -> m' b -> m (m' a))
backM u v m'c = do --  m'c :: Maybe C
    let f = ingredient2 (`u` m'c)
    m'b <- v
    f (pure m'b)

class BayesKleisliComposable m' where
    ingredient1 :: Monad m => (a -> m (m' b)) -> m' a -> m (m' b)
    ingredient2 :: Monad m => (m a -> m b) -> m (m' a) -> m (m' b)

instance BayesKleisliComposable Maybe where
    ingredient1 f ma = case ma of
        Just x -> f x
        Nothing -> return Nothing

    ingredient2 f mm'a = do
        m'a <- mm'a
        case m'a of
            Just b -> Just <$> f (pure b)
            Nothing -> return Nothing



{-
m (a -> b)

m (f (a -> b))

m (f a -> f b)

m f a -> m f b

-}







{-

f :: a -> m (Maybe b)
g :: b -> m (Maybe c)
g' :: m b -> Maybe c -> m b
f' :: m a -> Maybe b -> m a
------------------------------
goal :: m a -> Maybe c -> m a

solution 
ma              :: m a 
f =<< ma        :: m (Maybe b)
g' ?? (f =<< ma):: Maybe c -> m (Maybe b)
f' ma           :: Maybe b -> m a
g' ?? (f =<< ma) >=> f' ma :: Maybe c -> m a

(??) :: (m b -> Maybe c -> m b) -> m (Maybe b) -> (Maybe c -> m (Maybe b))
u ?? v = \maybeC -> do 
    maybeB <- v
    case maybeB of 
        Just b -> u (pure b) maybeC :: m b


fuseMaybe :: (Monad m) => m b -> m (maybe b)
fuseMaybe = fmap Just

vanilla version 
f :: a -> m b
g :: b -> m c
g' :: m b -> c -> m b
f' :: m a -> b -> m a
------------------------------
goal :: m a -> c -> m a


solution
ma :: m a 
f =<< ma  :: m b 
g' (f =<< ma) :: c -> m b
f' ma :: b -> m a 
g' (f =<< ma) >=> f' ma :: c -> ma

goal = \ma -> g' (f =<< ma) >=> f' ma






-}


{-|
`elabChannel'`
curly bracket indicates deterministic channel created by `fromFunc`
non-bracket (like kChannel) indicates stochastic channel

                                   [ProdRule a]                 ProdRule a
          --- {Left >>> legalRule} --->--------  chooseChannel ----
NT a     |                                                         |                   Maybe [Symbol a]
---->----+                                                         =={safeApplyRule} ------->---------   
         |               NT a                                      |     
          ---------->----------------------------------------------                        

-}


elabChannel :: (Grammar a,_) => NT a ⥂ Maybe [Symbol a]
elabChannel = dup >>> first (fromFunc (Left >>> legalRule) >>> chooseChannel) >>> fromFunc (uncurry safeApplyRule)

-- >>> enumerate $ back elabChannel (uniformD $ nts @Expr) (Just [Left NTExpr,Left NTExpr])
-- [(NTExpr,0.9999999999999999)]


testMapA :: _ => BayesChannel m [NT a] [Maybe [Symbol a]]
testMapA = mapA @[] elabChannel

-- >>> enumerate $ forw testMapA [NTExpr]
-- No instance for `Traversable Enumerator'
--   arising from a use of `testMapA'
-- In the first argument of `forw', namely `testMapA'
-- In the second argument of `($)', namely `forw testMapA [NTExpr]'
-- In the expression: enumerate $ forw testMapA [NTExpr]


elabChannel' :: Symbol Expr ⥂ Maybe [Symbol Expr]
elabChannel' = fromFunc (\case Left x -> Just x; Right _ -> Nothing) >>=> elabChannel

fanOut c1 c2 = dup >>> (c1 *** c2)

elabChannel2 :: MonadMeasure m => BayesChannel m [Symbol Expr] (Maybe [Symbol Expr])
elabChannel2 = ((fromFunc head  >>> elabChannel') `fanOut` fromFunc (Just . tail)) >>> fromFunc (uncurry (liftA2 (++)) )

elabN :: MonadMeasure m => Int -> BayesChannel m [Symbol Expr] _
elabN n =
    foldr (>>=>) elabChannel2 (replicate (n-1) elabChannel2) 




-- >>> enumerate $ forw (elabN 3)  ([Left (NTExpr)])
-- [(Just [Left NTExpr,Left NTExpr,Left NTExpr,Left NTExpr],0.36363636363636337),(Just [Left NTString,Left NTExpr,Left NTExpr],0.1818181818181817),(Just [Left NTInt,Left NTExpr,Left NTExpr],0.1818181818181817),(Nothing,9.090909090909086e-2),(Just [Right (TString "x"),Left NTExpr],9.090909090909086e-2),(Just [Right (TInt 42),Left NTExpr],9.090909090909086e-2)]

-- elabChannel'' :: _ => Either (Symbol Expr) () ⥂ Either (Symbol Expr) ()
-- elabChannel''=  left elabChannel' >>> (fromFunc head +++ fromFunc (const ()))


-- elabTwice :: Symbol Expr ⥂ Either [Symbol Expr] ()
-- elabTwice = elabChannel' 
--     >>> ((fromFunc head >>> first elabChannel') +++ id)



-- >>> enumerator $ forw elabTwice (Left NTExpr)
-- [(Just [Left NTExpr,Left NTExpr],0.4000000000000001),(Just [Left NTString],0.20000000000000004),(Just [Left NTInt],0.20000000000000004),(Just [Right (TString "x")],0.10000000000000002),(Just [Right (TInt 42)],0.10000000000000002)]




{-|
`testElab'`
curly bracket indicates deterministic channel created by `fromFunc`
non-bracket (like kChannel) indicates stochastic channel

                          [ProdRule a]          [Double]          Int  
                        ------->-------- {1 <$} --->---- kChannel ->-                           
Symbol a               |                                             |                        Prodrule a
---->---{legalRule} ---+                                             ==  {\(i,r) -> r !! i}  ------>-------
                       |  [ProdRule a]                               |  
                        ------->-------------------------------------                         



-}
testElab :: (MonadMeasure m, Grammar a, _) => BayesChannel m (Symbol a) (ProdRule a)
testElab = fromFunc legalRule >>> chooseChannel

-- >>> enumerate  $ back testElab (uniformD $ Left <$> nts) RString
-- [(Left NTString,0.9999999999999999)]



{-|`chooseChannel`

                              [a]               [Double]          Int  
                     ---------->-------- {1 <$} --->---- kChannel ->-                            
   [a]              |                                                |                         a
---->---{\x->(x,x)}=                                                  ==  {\(i,r) -> r !! i} -->--
                    |         [a]                                    |  
                     ---------->-------------------------------------                                                     

-}
chooseChannel :: (MonadMeasure m, Eq a) => BayesChannel m [a] a
chooseChannel = dup >>>
    first (fromFunc (1 <$) >>> kChannel)
    >>> fromFunc (uncurry . flip $ (!!))



ddd :: _ => _
ddd = enumerate $ back chooseChannel (uniformD [[3],[3,3]]) 3

-- >>> ddd
-- [([3],0.5000000000000002),([3,3],0.5000000000000001)]




toLog= Exp . log

distExpr :: MonadMeasure m => m [Double] -> m Expr
distExpr mw = do
    probs <- mw
    i <- categorical $ fromList probs
    score (toLog $ probs !!i)
    [Var <$> uniformD ["x","y","z"],
        Const <$> uniformD [42,59,71],
        Plus <$> distExpr mw <*> distExpr mw,
        Mult <$> distExpr mw <*> distExpr mw
        ] !! i

surface :: Expr -> String
surface = \case 
    Var x -> x 
    Const x -> show x 
    Plus x y -> "(" ++ surface x ++ " + " ++ surface y ++ ")"
    Mult x y -> "(" ++ surface x ++ " * " ++ surface y ++ ")"

inferW :: MonadMeasure m => _ -> String -> m Expr
inferW ma b = do 
    (e,logP) <- runWeightedT $ distExpr ma
    condition (surface e == b)
    score logP
    return e


distSur :: _ => _
distSur = fmap surface . distExpr 

every :: Int -> [a] -> [a]
every n xs = case drop (n -1) xs of
  (y : ys) -> y : every n ys
  
runThis = nub . take 10  . filter ((>0) . snd)<$> (Lazy.mh 1 $ inferW (fmap toList . dirichlet . fromList $ [5,5,1,1]) "(42 + 42) + (42 + 42)")


-- >>> runThis
-- ProgressCancelledException
