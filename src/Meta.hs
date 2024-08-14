{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Meta where
import Control.Monad.Bayes.Class
import Control.Monad.Bayes.Population (fromWeightedList)
import Text.Printf
import Data.Vector (fromList, toList)
import Control.Monad.Bayes.Sampler.Strict (sampler)
import Control.Monad.Bayes.Enumerator (toEmpirical)
import Control.Monad
import Data.Functor.Identity (Identity)
import Grammar


data RepSymbol = New | RepLoc Int | Star deriving (Show, Eq,Ord)
type Meta = [RepSymbol]

factorial :: Int -> Int
factorial n = product [1..n]


uniformPartitions :: (MonadDistribution m) => Int -> m [Int]
uniformPartitions n = do
    k <- categorical'  $  (\x -> (x,  fromIntegral x ^ n / fromIntegral (factorial  x))) <$> [1..]
    --replicateM n (uniformD [1..k])
    return [k]


-- >>> factorial <$> [1..100]
-- [1,2,6,24,120,720,5040,40320,362880,3628800,39916800,479001600,6227020800,87178291200,1307674368000,20922789888000,355687428096000,6402373705728000,121645100408832000,2432902008176640000,-4249290049419214848,-1250660718674968576,8128291617894825984,-7835185981329244160,7034535277573963776,-1569523520172457984,-5483646897237262336,-5968160532966932480,-7055958792655077376,-8764578968847253504,4999213071378415616,-6045878379276664832,3400198294675128320,4926277576697053184,6399018521010896896,9003737871877668864,1096907932701818880,4789013295250014208,2304077777655037952,-70609262346240000,-2894979756195840000,7538058755741581312,-7904866829883932672,2673996885588443136,-8797348664486920192,1150331055211806720,-1274672626173739008,-5844053835210817536,8789267254022766592,-3258495067890909184,-162551799050403840,-8452693550620999680,-5270900413883744256,-7927461244078915584,6711489344688881664,6908521828386340864,6404118670120845312,2504001392817995776,162129586585337856,-8718968878589280256,3098476543630901248,7638104968020361216,1585267068834414592,-9223372036854775808,-9223372036854775808,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]


-- >>> toEmpirical <$> replicateM 1000 (sampler (uniformPartitions 2 ))
-- ProgressCancelledException


-- >>> setPartition 4
-- [[1,1,1,1],[1,1,1,1],[1,1,1,2],[1,1,2,2],[1,2,2,2],[2,2,2,2],[1,1,1,1],[1,1,1,2],[1,1,2,2],[1,1,2,3],[1,2,2,2],[1,2,2,3],[1,2,3,3],[2,2,2,2],[2,2,2,3],[2,2,3,3],[2,3,3,3],[3,3,3,3],[1,1,1,1],[1,1,1,2],[1,1,2,2],[1,1,2,3],[1,2,2,2],[1,2,2,3],[1,2,3,3],[1,2,3,4],[2,2,2,2],[2,2,2,3],[2,2,3,3],[2,2,3,4],[2,3,3,3],[2,3,3,4],[2,3,4,4],[3,3,3,3],[3,3,3,4],[3,3,4,4],[3,4,4,4],[4,4,4,4]]


useMeta' :: Meta -> a -> [a] -> [a] -> [a]
useMeta' [] _ _ done = done
useMeta' (m:ms) r xs done = case m of
    New      -> useMeta' ms r (tail xs) (done ++ [head xs])
    Star     -> useMeta' ms r xs (done ++ [r])
    RepLoc i -> useMeta' ms r xs (done ++ [done !! i])

useMeta :: Meta -> a -> [a] -> [a]
useMeta ms r xs = useMeta' ms r xs []

simplifyByMeta :: Meta -> [a] -> [a]
simplifyByMeta m xs = [x | (s,x) <- zip m xs, s == New]


freeVar :: Meta -> Int
freeVar = foldr (\x -> if x == New then (+1) else id) 0


{-| Generative Process of RepSymbol.
Model Parameter: 
    w    ~ Dir(1,1,1)  --  weights for choosing New, Star and Repeat.
    wR n ~ Dir(1,..)   --  weights for choosing fresh variable class among n choices.
Model Input:
    [Int]   -- locations of existing fresh variables 

Model Output:
    RepSymbol -- What to do on the current variable (fresh variable, copy parent, copy the ith sibling)
-}
distRepSymbol :: MonadDistribution m
    => Double               -- ^ weight for using a fresh variable
    -> Double               -- ^ weight for repeating the parent 
    -> Double               -- ^ weight for repeating a sibling 
    -> (Int -> [Double])    -- ^ weights for n choices
    -> [Int]                -- ^ positions of previous repeatable fresh variables
    -> Bool                 -- ^ Whether the current position can copy root
    -> m RepSymbol
distRepSymbol wNew wStar wRep f ns canStar = do
    let n = length ns
    topLevelChoice <- case (ns,canStar) of
        ([],False) -> return "New"
        ([],True)  -> categorical' $ zip ["New","Star"] [wNew,wStar]
        (_,False)  -> categorical' $ zip ["New","Rep"] [wNew,wRep]
        (_,True)   -> categorical' $ zip ["New","Rep","Star"] [wNew,wRep,wStar]
    case topLevelChoice of
        "New" -> return New
        "Star" -> return Star
        "Rep" -> do
            i <- categorical $ fromList (f n)
            return $ RepLoc (ns !! i)
        _ -> error $ printf "impossible topLevelChoice of %d" topLevelChoice

{-| Generative Process of a meta-rule of length n
Model Parameter: 
    w    ~ Dir(1,1,1)  --  weights for choosing New, Star and Repeat.
    wR n ~ Dir(1,..)   --  weights for choosing fresh variable class among n choices.

Model Input:
    n -- the length of the meta-rule

Model Output:
    Meta
-}



distMeta' :: (MonadDistribution m , Eq a) => a -> [a] -> Double -> Double -> Double -> (Int -> [Double])  -> m Meta
distMeta' _ [] _ _ _ _ = return []
distMeta' r (g:gs) wNew wStar wRep f  = do
    xs  <- distMeta' r gs wNew wStar wRep f
    let wNew' = if nonempty xs && all (==New) xs then 0 else wNew  
        nonempty = not . null
    x   <- distRepSymbol wNew' wStar wRep f [i | (i,x) <- zip [0..] xs, x==New && gs!!i == g] (g==r)
    return (xs ++ [x])
    

distMeta :: (MonadDistribution m, Eq a) => a -> [a] -> Double -> Double -> Double -> (Int -> [Double]) -> m Meta
distMeta r gs = distMeta' r (reverse gs)


test = toEmpirical <$> (sampler . replicateM 5000 $ distMeta "x" ["x","x","x"] 1 1 1 (`replicate` 1) )

-- >>> test
-- [([Star,Star,New],0.1294),([Star,Star,Star],0.1234),([Star,New,Star],8.84e-2),([Star,New,RepLoc 1],8.52e-2),([New,RepLoc 0,RepLoc 0],8.44e-2),([New,Star,Star],8.44e-2),([New,Star,RepLoc 0],8.38e-2),([New,RepLoc 0,New],8.24e-2),([New,Star,New],8.02e-2),([Star,New,New],8.0e-2),([New,RepLoc 0,Star],7.84e-2)]


data Abstraction a
    = Abstraction a
    | Compose Int (Abstraction a) (Abstraction a)
    | ApplyMeta Meta (Abstraction a) [Abstraction a]
    deriving (Show,Eq,Ord)

class Arity a where
    arity :: a -> Int

instance (Grammar a) => Arity (ProdRule a) where
    arity = nArg

instance Arity a => Arity (Abstraction a) where
    arity (Abstraction x) = arity x
    arity (Compose _ x y) = arity x + arity y - 1
    arity (ApplyMeta m a as) = sum $ arity <$> useMeta m a as

class ArgTypes a b where
    argTypes :: a -> [b]

instance (Grammar a) => ArgTypes (ProdRule a) (Symbol a) where
    argTypes = argSymbol

instance ArgTypes a b=> ArgTypes (Abstraction a) b where
    argTypes (Abstraction x) = argTypes x
    argTypes (Compose i x y) = take (i-1) (argTypes x) ++ argTypes y ++ drop i (argTypes x)
    argTypes (ApplyMeta m a as) = foldMap argTypes (useMeta m a as)

data TemplateParams m a = TemplateParams {
    dMeta :: Symbol a -> [Symbol a] -> m Meta,  -- ^ p (meta rule | freeVar, rootNt, list of symbols (goals))
    dProd :: Symbol a -> m (ProdRule a),        -- ^ p (production rule | symbol )
    weightChoose :: m [Double]                  -- ^ p (weight) to choice among Abstraction, Compose or ApplyMeta when the compose and apply meta are non trivial
}

distAbstraction :: (MonadDistribution m, Grammar a)
    => Symbol a                         -- ^ output type of the abstraction 
    -> TemplateParams m a                 
    -> m (Abstraction (ProdRule a))     -- ^ p (abstraction)
distAbstraction goal p = do
    w <- weightChoose p
    tag <- categorical' $ zip ["Abstraction","Compose","ApplyMeta"] w
    case tag of
        "Abstraction" -> do
            r <- dProd p goal
            return $ Abstraction r
        "Compose" ->  do
            a <- distAbstraction goal p
            case arity a of
                0 -> return a
                n -> do
                    i <- categorical . fromList $ replicate n 1 -- decide which position to compose
                    let goal' = argTypes a !! i -- the goal in position i
                    a' <- distAbstraction goal' p -- sample an abstraction that produces this goal
                    return $ Compose i a a'
        "ApplyMeta" -> do
            a <- distAbstraction goal p
            m <- dMeta p goal (argTypes a) -- sample a meta rule that is compatible with the arg types. 
            let subgoals = simplifyByMeta m (argTypes a)
            as <- sequence [distAbstraction g p | g <- subgoals] -- sample a list of rules that produces the list of subgoals
            return $ ApplyMeta m a as
        _ -> error $ "impossible tag" ++ tag

priorParam :: _ => TemplateParams m a
priorParam = TemplateParams {
    dMeta = \x xs -> distMeta x xs 1 1 1 (`replicate` 1),   -- prior of the parameters for sampling meta rules 
    dProd = \x -> case legalRule x of
            [] -> error $ "no legal rule for "++ show x
            rs -> categorical' . fmap ( ,1) $ rs,           -- priors for the rule distribution for each symbol 
    weightChoose = toList <$> dirichlet (fromList [1,1,1])  -- prior for categorical weight  
}


priorAbstraction :: (MonadDistribution m, Grammar a, _) => m (Abstraction (ProdRule a))
priorAbstraction  = distAbstraction begin priorParam

categorical' :: MonadDistribution m => [(a,Double)] -> m a
categorical' xs = do
    let weights = snd <$> xs
        choices = fst <$> xs
    n <- categorical $ fromList weights
    return (choices !! n)


res :: _ => m (Abstraction (ProdRule Expr))
res = priorAbstraction
-- >>>  sampler res
-- ApplyMeta [] (ApplyMeta [New] (Compose 0 (Abstraction RConst) (ApplyMeta [] (ApplyMeta [] (Abstraction RInt) []) [])) [ApplyMeta [] (ApplyMeta [] (Abstraction RInt) []) []]) []

-- >>> sampler (priorAbstraction @_ @Expr)
-- ApplyMeta [New,Star] (Abstraction RPlus) [Abstraction RVar]

