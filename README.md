
# Stochastic Memoization

![Grammar rules](/img/grammarFragments.svg)

What you see here is a number of partially completed syntax trees, or *fragments*. Some of these correspond to familiar grammatical rules, like "S -> NP VP", while others are terminal rules, like "DET -> the". Finally, there are fragments which fall in neither category, like the tree labelled VP. 

[Productivity and Reuse in Language](https://mitpress.mit.edu/books/productivity-and-reuse-language) is a book and research program which presents a really beautiful proposal for how an agent comes to store grammatical units.

Central to the story is a probabilistic generative model of syntax trees, which are created (roughly) as follows. Starting at a given node, you either choose to branch to a left and right node (where the process repeats), terminate with a leaf node, or insert a whole fragment into the tree from your cache of fragments.

When it comes to implementing complex probabilistic recursion schemes elegantly and efficiently, Haskell is a very appealing choice. It is able to separate complex problems along the grain of their abstract elements (here, the unfolding of recursive structures, and probabilistic programming).

In particular, the problem of stochastically generating (possibly partial) trees involves two things that Haskell can do very beautifully:

1. [Folding and unfolding (co)recursive data](https://maartenfokkinga.github.io/utwente/mmf91m.pdf)
2. Writing probabilistic programs](http://denotational.co.uk/publications/scibior-kammar-ghahramani-funcitonal-programming-for-modular-bayesian-inference.pdf)

# To run

Download the Haskell Stack tool. Do:

stack build

stack ghci

# Walkthrough

The core functionality of the library is in `fragmentGrammar` which probabilistically generates trees while stochastically caching tree fragments. This is complicated, so I'll build up to it step by step. (I'm assuming that the reader is familiar with Haskell at an intermediate level.)

## The datatypes

```haskell
data NonRecursiveTree a x =
  Leaf a
  | Branch NodeData [x]
```

where `NodeData` records some information at each node (e.g. the syntactic category).

As the name suggests, the `NonRecursiveTree` type is not recursive; it's just one n-ary branching tree "layer". `a` is the type of a leaf, and `x` is the type of each branch.

The type of a full tree is then:

```haskell
type Tree a = NonRecursiveTree a (Tree a)
```

Or more succintly, using Haskell's nice propensity for abstracting away recursion even at the type level:

```haskell
type Tree a = Fix (NonRecursiveTree a)
```

Meanwhile, the type of a fragment is:

```haskell
type Fragment leafType = Free (NonRecursiveTree leafType) CAT

```

where `Free`, from the library Control.Monad.Trans.Free, is defined as:

```haskell
data Free f a = Pure a | Free (f (Free f a))
```

You can think of `Free` as being like `Fix`, but with the option of "pausing" with a value of some type, here specified as `CAT`. So, a fragment is precisely a tree where at any node, we may stop there, instead of continuing with a branch or leaf.

In fact, instead of having `Tree` be defined using `Fix`, we can define it as:

```haskell
type Tree a = Free (NonRecursiveTree a) Void
```

`Void` is the type with no inhabitants, so this is saying: a `Tree` is a `Fragment` where the type of the pausing values is the empty type: in other words, there's no way to pause.

Formulating `Tree` in this way is convenient, because there are some powerful things we can do with `Free` that we can't do with `Fix`. 

In particular, `Free` has a generalized form which `Fix` does not:

```haskell
newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }
```

When `m` is `Identity`, then `FreeT f Identity a` is isomorphic to `Free f a` (although the version of `Free f a` we need from Control.Monad.Free, requires us to perform a simple conversion). But in general, we're going to let `m` be an arbitrary monad: this is what will allow us to move from deterministic unfolding of trees to probabilistic unfolding, because probability distributions form a monad.

Here then are the relevant types in their full complexity:

```haskell
type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity
type Tree m leafType = FT.FreeT (NonRecursiveTree leafType) m Void
type Fragment m leafType = FT.FreeT (NonRecursiveTree leafType) m CAT
```


## Unfolding a tree

The *recursion-schemes* documentation has this to say:

> "The core idea of this library is that instead of writing recursive functions on a recursive datatype, we prefer to write non-recursive functions on a related, non-recursive datatype we call the "base functor"."

In our case, the "base functor" is `NonRecursiveTree Word`, (where `Word` is currently just set to be a synonym for the type `String`) and the recursive type is going to be either `Tree m Word` or `Fragment m Word`, for some monad `m`. OK, strictly speaking, the base functor is a bit more complicated, but you get the idea.

The first thing we want to do is to deterministically make a tree of type `Tree Deterministic Word`, by starting with a seed. Let's say that the seed is of type `CAT` (for "category"), defined as:

```haskell
data CAT = S | NP | VP | A | N | DET | COP | V
```

What's particularly nice about *recursion-schemes* is its generality. The function `unfold` has type:

```haskell
unfold :: Corecursive t => (a -> Base t a) -> a -> t
```

This expresses what it means to unfold not just a binary branching tree, but in fact any kind of (co)recursive structure. This will prove particularly useful.

But for now, let's note that a special case of the beautiful general type of `unfold` is the following:

```haskell
unfold :: (CAT -> Fold.Base (Tree Deterministic Word) CAT) -> CAT -> Tree Deterministic Word
```

Then we can make the tree as follows:

```haskell
deterministicSimpleTree :: Tree Deterministic Word
deterministicSimpleTree = Fold.unfold (Compose . Identity . \case

  S  -> Branch S [NP, VP]
  NP ->  Branch S [DET, N]
  DET -> Leaf "the"
  N  -> Leaf "cat"
  VP ->  Branch VP [V, NP]
  V  -> Leaf "sees") 

  S -- starting category
```

This produces:

![Deterministic Simple Tree](/img/deterministicSimpleTree.svg)


## Making this procedure richer

What we have now is not very useful though: the tree that gets output is always the same, and no tree fragments are stored or used. Accordingly, there are three independent enhancements we want to make:

1. Produce fragments
2. Use fragments
3. Unfold trees (and/or fragments) probabilistically.

First, problem 1:

```haskell
deterministicSimpleFragment :: Fragment Deterministic Word
deterministicSimpleFragment = Fold.unfold (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf "the"
  N  -> leaf "cat"
  VP ->  pauseAt VP
  V  -> leaf "sees") 

  S 
```

This is the code to deterministically produce a fragment, as shown here:

![Deterministic Simple Fragment](/img/deterministicSimpleFragment.svg)


Next, problem 2. We want to be able to not only generate fragments, but to use them in the recursive unfolding of a tree (or indeed or a fragment). That is, we want to have the option of sticking in a whole fragment at a node, and then continuing from there.

The solution for this is pre-made by *recursion-schemes*. The key is to use a different, more powerful pattern of recursion called *futu*, which has the following form:

```haskell
futu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
```

This looks intimidating, but specializing to our case, gives *exactly* what we want:

```haskell
Fold.futu :: (CAT -> Fragment m Word) -> CAT -> Tree m Word
```

(Actually, this is a slight lie: the type is merely isomorphic to the above, but that amounts to the same thing).

If it's not clear what's going on here, then the idea is that *futu* allows you to specify multiple future steps of the recursion in the form of a Free monad over your base functor, but that is precisely what a fragment is!

So, we can use fragments as follows:

```haskell

type FragmentDict = CAT -> [Fragment Deterministic Word]

deterministicComplexTree :: FragmentDict -> Tree Deterministic Word
deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET -> leaf "the"
  N  -> leaf "cat"
  VP -> head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
  V  -> leaf "sees"
  ) 

  S

  where 

  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)
```

The line with `VP` is a case of a pre-existing fragment being used. The functions `loadFragments` and `fragmentToBranch` exist for technical reasons related to the slight lie I alluded to above.

This produces:

![Deterministic Complex Tree](/img/deterministicComplexTree.svg)

What's really cool about this is that typical CFG rules like 'S -> NP VP' can be regarded as fragments, as can rules like 'N -> "cat" '. So instead of having a separation between the grammar and a collection of fragments, we can simply express all the productive rules of our grammar as fragments. 

## Using a monad other than Identity

Soon, we'll want to use a monad representing probability distributions, but as a more familiar example, we can use the list monad to generate a Context Free Grammar:

```haskell
fragmentCFG :: FragmentDict -> Tree [] Word
fragmentCFG fragmentDict = Fold.futu (Compose . \case

  S  -> return $ branch (S, False) [NP, VP]
  NP ->  return $ branch (NP, False) [DET, N]
  DET -> return $ leaf (DET, False) "the"
  N  ->  [branch (N, False) [A, N], leaf (N, False) "idea"]
  A  ->  [leaf (A, False) "green", leaf (A, False) "furious"]
  VP ->  (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
  V  -> return $ leaf (V, False) "sees")
  
  S

  where 

  branch a bs = FT.Free $ Branch a (F.Pure <$> bs) 
```

You may be wondering how to actually get trees from it, and the answer is by using the following:

```haskell
joinFreeT :: (Monad m, Traversable f) => FreeT f m a -> m (Free f a)
```

Then, we can do:

```haskell
main = print $ FT.joinFreeT $ fragmentCFG grammar
```

That's an infinite list of trees though, so we should do something about that. We can use the powerful `cutoff` function to throw out trees of excessive depth, as in:

```haskell
atDepth = 5
main = print $ FT.joinFreeT $ FT.cutoff atDepth $ fragmentCFG grammar
```

With a bit more processing in that vein, we get:

![](/img/fragmentCFG.svg)


## Incorporating Probability 

We will use a library called *monad-bayes*. This defines a typeclass `MonadSample` of probability monads we can sample from. Here's an example:

```haskell
probabilityExample :: MonadSample m => m Double
probabilityExample = do
  x <- bernoulli 0.5
  y <- Control.Monad.Bayes.Class.normal 0 1
  return (if x then y else 3)
  

runProbabilityExample :: IO ()
runProbabilityExample = print =<< sampleIO probabilityExample
```

Here, we use `sampleIO`, which instantiates the sampling monad to be naive sampling with a random number generator, and proceeds from there. But what's nice is that `probabilityExample` is not tied to this implementation detail of our inference method: it's really just an abstract declaration of a particular distribution. This separation of model and inference is often mentioned in the context of probabilistic programming.

## Unfolding probabilistically

Changing our monad from `Deterministic`, we can obtain:

```haskell
probabilisticSimpleTree :: MonadSample m => Tree m Word
probabilisticSimpleTree = Fold.unfold (Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf "the"
  N  -> uniformD [branch N [A, N], leaf "idea"]
  A  -> uniformD [leaf "green", leaf "furious"]
  VP ->  return $ branch NP [V, NP]
  V  -> return $ leaf "sees")

  S
```

which is a simple PCFG. 

Then we can do:

```haskell
makeTree :: IO (Tree Deterministic Word)
makeTree = sampleIO $ FT.joinFreeT probabilisticSimpleTree
```


## A full fragment grammar

Putting all this together leads to a probabilistic grammar which produces a fragment, but also uses a corpus of fragments to do so:

```haskell
fragmentGrammar :: MonadSample m => FragmentDict -> Fragment m Word
fragmentGrammar fragmentDict = Fold.futu go S where
  
  howMuchToReuse = 1.0
  howMuchToSuspend = 0.5
  howMuchToRecurse = 0.5
  
  go cat = Compose $ do

    reuse <- bernoulli howMuchToReuse
    
    if reuse && not (null (fragmentDict cat)) then uniformD (FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) . fragmentToBranch <$> (fragmentDict cat))
    else do
      recurse <- bernoulli howMuchToRecurse
      if recurse then makeBranches cat else FT.Free . Leaf <$> uniformD words 

  makeBranchCompositional = do
    suspend <- bernoulli howMuchToSuspend
    cat <- uniformD cats
    return $ if suspend then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

  makeBranches cat = do
    bL <- makeBranchCompositional
    bR <- makeBranchCompositional
    return (FT.Free $ Branch cat [bL, bR] )
```

Here's what this does. At each step of the unfolding, we do as follows: with some probability linked to the number of existing fragments, we decide whether to get a fragment from the cache. If we do get one from the cache, we will use it to continue the unfolding. If not, we will proceed compositionally.

This whole process produces a new fragment, so we can repeat it many times, accumulating a larger and larger store of fragments. We could also have used the state monad transformer on top of the probability monad, to cache fragments during the unfolding; that works, but seems unnecessary.

## Visualization

It is pleasing to note that while the creation of a tree involves an unfolding, the transformation of a tree into a visualization is the dual operation, of folding. Naturally, recursion-schemes provides, for every unfolding operation, its dual folding operation.

We create visualizations using the excellent *diagrams* package (actually it's several linked packages). *diagrams* provides a DSL in Haskell for compositionally generating diagrams, which is what I use for the images throughout.

Folding is also how we take a syntax tree and produce a meaning. The dual of the `futu` recursion scheme is `histo`, and it makes sense to use this to interpret a syntax tree in an idiom aware way. Composing them gives `chrono`, which unfolds to produce a tree, and then folds it back down again. I might use that as a way of generating sentence meanings randomly. 

## Inference

The reason we use *monad-bayes* is that if you define something generically in terms of the MonadSample and MonadInfer classes, it provides a range of inference algorithms like MCMC, and methods for customizing your own inference.

In general, we want to ask questions like: given the generative process described by `fragmentGammar`, and given a set of observed sentences, what must the set of fragments have been to have resulted in the generation of those sentences.

This is an *extremely* challenging inference problem, and just using MCMC out of the box is beyond hopeless. But as I better understand inference in this domain, I hope to use the tools of *monad-bayes* to implement something tractable. 


