# Template Grammar

Recall that a Template Grammar $T_G$ over a Context-free grammar $G$ is defined as

``` Haskell
data Template r 
  := Rule r
  |  Comp Int (Template r) (Template r)
  |  WithRep (Template r) Meta [Template r]
```

1. Rule Lifting
2. Partial Composition
3. Repetition

Claim 1: The first two axioms gives the expressive power of the tree adjoining grammar.

First let's give the tree-adjoining grammar a functional interpretation.
There are two operations in TAG: Substitution and Adjunction. We will show that
they are essentially function composition.

An initial tree `t1` headed by `x` with substitution nodes `y` and `z` can be interpreted as a function
`f : y × z -> x`. Tree substitution is then partial composition. For example, if there is a initial tree `t2`
headed by z with substitution nodes `a`, `b`, `c`, then the initial tree obtained by substituting the node `z` with `t2` is a function
$$h : Y × A × B × C \to X$$

$$h(y, a, b, c) = f(y,g(a,b,c))$$

# Parsing Template Grammar

```
Item := NT × Template × [Maybe [T]]
```

```
Deduction rules for parsing Template Grammar

Template Grammar of rank k specifies a set of elementary template of arity <= 2 
new template can only be formed when its arity is <= 2  

case of Elementary template 

    
    ---------------------------- evidenceOf E X = e
    (X, E, e)

case of WithRep on general meta-rule
    α : A1...An -> X, meta : (A1...Ak) -> (A1...An), 
    [A1,α1,l1] ... [Ak,αk,lk]
    ------------------------------------------------
    [X , WithRep α meta [α1...αk] , sum [l1...lk]]

case of Comp i α β
    α : A1...An -> X, β : B1 ... Bm -> Ai,
    ins α ! i == out β
    [X,α,front1], [Ai,β,front2]
    ------------------------------------------------
    [X, Comp i α β, `fillNthHoleby` i front2 front1 ]


```

```haskell
mergeComp1_0_l:: ((),[a]) -> [a] -> [a]
mergeComp1_0_r:: ([a],()) -> [a] -> [a]

mergeComp1_1_l_l:: ((),[a]) -> ((),[a]) -> ((),[a],[a])
mergeComp1_1_l_r:: ((),[a]) -> ([a],()) -> ([a],(),[a])
mergeComp1_1_r_l:: ([a],()) -> ((),[a]) -> ([a],(),[a])
mergeComp1_1_r_r:: ([a],()) -> ([a],()) -> ([a],[a],())

mergeComp2_0_lm_l :: ((),(),[a]) -> [a] -> ([a],(),[a])
mergeComp2_0_lm_m :: ((),(),[a]) -> [a] -> ((),[a],[a])
mergeComp2_0_lr_l :: ((),[a],()) -> [a] -> ([a],[a],())
mergeComp2_0_lr_r :: ((),[a],()) -> [a] -> ((),[a],[a])
mergeComp2_0_mr_m :: ([a],(),()) -> [a] -> ([a],[a],())
mergeComp2_0_mr_r :: ([a],(),()) -> [a] -> ([a],(),[a])

frontierForm :: Template a -> [Bool]
frontierForm = \case 
  Template r -> replicate (arity r) True 
  Comp i x y ->  (frontierForm x) `filledBy` [frontierForm y]
  WithRep x m ys -> 
    (frontierForm x) `filledBy` (frontierForm <$> ys)


```

Parsing as composition of preimages of the generateAll function
