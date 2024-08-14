

Domain specific grammar | Template grammar
|
lexicon


The proposed template grammar is a meta theory encodes an inductive bias over the ways in which a larger structures constructed using repeated sub-structures. 

We want this inductive bias to be 1. simple 2. self-evident. 

Assumption 1 (Encapsulation of composite constructions). 

If we know a way to construct a structure $S$ using substructures $S_1 ... S_n$, and we know how to construct one of the substructure $S_i$ using its substructure $S{i_1} ... S{i_m}$, then there is a new way to construct $S$ using $S_1 ... S_{i_1} ... S_{i_m} ... S_n$ by composing the two steps. 

The point here is not that it is possible the model can sample two constructions in succession, but that it reserves probability to sample the succession as a whole in a single step.

Formally, given a function $ g : \prod_{i\in I_g} S_{g_i} \to S $ and a function $ f : \prod_{i \in I_f } S_{f_i} \to S_{g_k}$, our theory-making machine should be able to encapsulate $g \circ f$ as a single construction principle. 

We will later refer to the encapsulated constructions as "templates".


Assumption 2 (Encapsulation of repetitions)

We can understand a sequence of entities as generated in a two stage process seperating repetition and the contents for the repetition. 
```
           p ~ reptitionPattern  --        p : List S -> List S 
     content ~ substructures p   --  content : List S
let sequence = use p content     -- sequence : List S
return (use p content)
```


Motivation: Suppose that we do not have this mechanism in the generative model. 







Definition (Template)

Given a set of merge rules $R$ (functions of type $(NT + T)^* \to NT$), the corresponding template $T_R$ is defined constructively by the following three axioms:

1. $\forall f \in R, \exist t \in T_R$.

2. Let $i \in \mathbb{N}$, $t_1,t_2 \in T_R$, if $argType_i(t_1) = Codomain(t_2)$, then $\exist t\in T_R$.

3. Let $m,n\in \mathbb{N}$, $t\in T_R$, $r \in Meta_{m,n}$, if r is compatible with t, then for any $\{t_i\}_{i=1}^m \in T_R^m$, $\exist t\in T_R$

```haskell
data Template a where 
  Template :: a -> Template a 
  Compose  ::  Natural -> Template a -> Template a -> Template a 
  ApplyMeta :: Template a -> Meta -> [Template a] -> Template a
```




#### Generative Process for $T_G$
Compared to PCFG 
```haskell
sampleTree :: (Grammar a) => Symbol a -> Distribution (Tree (Symbol a))
sampleTree x = do 
    rule ~ legalRule x 
    let xs = applyRule rule x 
    return (Node x (samplerTree <$> xs))
```


A Template is sampled by the following probabilistic program:

```haskell
sampleTemplate' :: (Grammar a) => Symbol a -> Distribution (Template (ProdRule a))
sampleTemplate' headSymbol = do
  constructor ~ categorical [1,1,1] -- categorical prior for template constructors
  case constructor of
    Template -> do 
      rule ~ sampleProductionRule (headSymbol)
      return (Template rule)
    Compose -> do 
      t1 ~ sampleTemplate' (headSymbol)
      i ~ uniformD [0.. arity (t1)] -- uniform prior for which position for composing templates
      t2 ~ sampleTemplate' (argSymbol i t1)
      return (Compose i t1 t2)
    ApplyMeta -> do 
      t ~ sampleTemplate' (headSymbol)
      mt ~ sampleMeta headSymbol (argSymbols t)
      ts ~ sampleTemplate' <$> freeSymbols t mt
      return (ApplyMeta t mt ts)

sampleTemplate :: (Grammar a) => Distribution (Template a)
sampleTemplate = sampleTemplate' startSymbol

```

The helper function `sampleTemplate'` takes a target symbol as an argument. It is used to control the root of the tree which the template represent. 
`sampleTemplate'` is defined recursively with varying target symbols as input.
`sampleTemplate` is the special case of `sampleTemplate'` where the root of the tree is the start symbol of the grammar.

Now we need to fill in the definition of the following probabilistic programs used in the definition of `sampleTemplate'`:

```haskell

sampleProductionRule :: (Grammar a) => Symbol a -> Distribution (ProdRule a)
sampleProductionRule headSymbol = do 
  weights ~ dir {1}^n where n = length (legalRules headSymbol) -- dirichlet prior for the weight of the categorical distribution
  rule ~ categorical weights
  return rule


sampleMeta :: (Grammar a) => Symbol a -> [Symbol a] -> Distribution Meta
sampleMeta


```



