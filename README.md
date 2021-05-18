UNDER CONSTRUCTION

# Stochastic Memoization

TODO: diagram

	What you see here is a sequence of trees which have been probabilistically generated. In the process of generating them, a number of "fragments", or partially complete trees, have been stored and reused. These are shown in the red box at the bottom of the diagram
TODO.



In BOOK TODO

	TODO
	lays out a beautiful proposal for how language comes to  

	a grammar is a process to generate sentences
	More recently, 
		Bayesian view, in which that process is probabilistic, and an agent performs *inference*, asking: given that I heard a sentence, what must the 
		A second, related question, which is easy to ask in this Bayesian framework is: what must the rules of the grammar...

Haskell is the ideal language for this problem. It is able to separate complex problems along the grain of their abstract elements (here, unfolding of recursive structures, and probabilistic programming), so that instead of writing brittle unreadable code where implementation details are intermingled with algorithmic ones, what you write is flexible and clear. The price for this is not speed (Haskell is extremely fast) but the need to work with mathematical abstractions.

In particular, the problem of stochastically generating (possibly partial) trees involves two things that Haskell can do very beautifully:

1. Folding and unfolding (co)recursive data: see https://maartenfokkinga.github.io/utwente/mmf91m.pdf
2. Writing probabilistic programs: see http://denotational.co.uk/publications/scibior-kammar-ghahramani-funcitonal-programming-for-modular-bayesian-inference.pdf

The *recursion-schemes* library captures the essence of what it means to unfold a data structure, while the *monad-bayes* library captures the essence of what it means to write a probabilistic program, so the main contribution of this project is to put those two things together.

# To run

Download the Haskell Stack tool. Do:

stack build
stack ghci

This second command will open a repl, in which you can write "makeDiagram" to generate sentences and corresponding diagrams

# Walkthrough

The core functionality of the library is in `fragmentGrammar` which probabilistically generates trees while stochastically caching tree fragments. This is complicated, so I'll build up to it step by step. (I'm assuming that the reader is familiar with Haskell at an intermediate level.)

## Step 1: The datatype

```haskell
data NonRecursiveTree a x =
  Leaf a
  | Branch NodeData [x]
```

where `NodeData` records some information at each node (e.g. the syntactic category).

As the name suggests, the `NonRecursiveTree` type is not recursive; it's just one n-ary branching tree "layer". `a` is the type of a leaf, and `x` is the type of each branch.

The type of a full tree is then:

```haskell
type RecursiveTree a = NonRecursiveTree a (RecursiveTree a)
```

Or more succintly:

```haskell
type RecursiveTree a = Fix (RecursiveTree a)
```

Note the recursion. This type isn't actually going to feature in the code, because all the functions we write will be on `NonRecursiveTree`. Why? The answer is nicely put in the docs of the library we use for our tree unfolding, *recursion-schemes*:

> "The core idea of this library is that instead of writing recursive functions on a recursive datatype, we prefer to write non-recursive functions on a related, non-recursive datatype we call the "base functor"."

In our case, the "base functor" is `NonRecursiveTree Word`, (where `Word` is currently just set to be a synonym for the type `String`) and the recursive type is going to vary, depending on whether we want to produce a tree, a partially complete tree, a probability distribution over trees, and so on.

## Step 2: Unfolding a tree

The first thing we want to do is to make a tree of type `RecursiveTree Word`, by starting with a seed. Let's say that the seed is of type `CAT` (for "category"), defined as:

```haskell
data CAT = S' | NP' | VP' | A' | N' | DET' | COP' | V'
```

What's particularly nice about *recursion-schemes* is its generality. The function `unfold` has type:

```haskell
unfold :: Corecursive t => (a -> Base t a) -> a -> t
```

This expresses what it means to unfold not just a binary branching tree, but in fact any kind of (co)recursive structure. This will prove particularly useful.

But for now, let's note that a special case of the beautiful general type of `unfold` is the following:

```haskell
unfold :: (CAT -> NonRecursiveTree Word CAT) -> CAT -> RecursiveTree Word
```

Then we can make the tree as follows:

```haskell
deterministicSimpleTree :: RecursiveTree Deterministic Word
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

![Deterministic Simple Tree](/img/deterministicSimpleTree.png)


## Step 3: tree fragments

What we have now is not very useful though: the tree that gets output is always the same, and no tree fragments are stored. Let's deal with the issue of fragments first. To do this, we introduce a new recursive type:


```haskell
type Fragment = Free (NonRecursiveTree Word) CAT

```


where `Free`, from the library Control.Monad.Trans.Free, is defined as:

```haskell
data Free f a = Pure a | Free (f (Free f a))
```

Here are some examples of values of type `Fragment`:

```haskell
examples :: [Fragment]
examples = [FT.free $ FT.Pure S,
            FT.free (FT.Free (Branch
	            (FT.free $ FT.Pure NP) 
	            (FT.free $ FT.Pure VP)))
	       ]

```

And here they are visualized:

TODO


So a `Fragment` is a tree where, optionally, the descent to the leaves may stop at some node and go no further. The computation has been "paused" before getting all the way to all the leaves.

Like `Fix (NonRecursiveTree Word)`, `Free (NonRecursiveTree Word) CAT` is a corecursive type, so `unfold` works on it.


Now, as mentioned, `unfold` in *recursion-schemes* is delightfully general, and so knows that `Free f a` is something which you can make with an `unfold`. So again, we have a (now different) special case of the type of `unfold`:


```haskell
unfold :: (CAT -> NonRecursiveTree Word CAT) -> CAT -> Free (NonRecursiveTree Word) TODO CHECK
```

## Step 4: unfold a tree using fragments

The next order of business (step 4) is to generate whole trees, but to use fragments in the process. That is, at a given node, rather than proceeding with a left branch and a right branch, we have the option of sticking in a fragment. This diagram illustrates the idea:

TODO

How to do this? It turns out that Data.Functor.Foldable has some other unfolding patterns which are fancier than `unfold`, and these are just what we need. First there's `apo`, which allows you to stick in fully complete trees at a given node. But we want to next, fancier, thing: `futu`: 


```haskell
futu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
```

Or specializing this to our use case, (t = RecursiveTree Word):

```haskell
futu :: (CAT -> NonRecursiveTree Word Fragment) -> CAT -> RecursiveTree Word
```

This means, if you give me a function which takes a `CAT` and produces two branches containing fragments (or just a leaf), I will give you a tree. 

TODO: make a diagram

## Step 5: Probability 

We will use a library called monad-bayes. This defines a typeclass `MonadSample` of monads we can sample from. Here's an example:

```haskell
TODO

probabilityExample = do
  

runProbabilityExample :: IO ()
runP...

TODO
```

The takeaway here is that probability distributions form a monad, so what we need is a way to add a monad to our unfolding process. 

## Step 6: unfolding with a monad

At first glance, *recursion-schemes* has no function called something like `unfoldM` which you might expect to find, as a monadic equivalent to `unfold`. But this is because you don't need it, as we'll see. But first, a new datatype, from the package *free*:


```haskell
data FreeF f a b = Pure a | Free (f b)
data FreeT f m a = FreeT {runFreeT :: m (FreeF f a (FreeT f m a))}
```

`FreeT m (NonRecursiveTree Word) CAT` is precisely a tree, or fragment of a tree, where each succesive layer is wrapped in a new layer of the monad `m`. A very handy function provided by the *free* package is `joinFreeT`:

```haskell
joinFreeT :: (Monad m, Traversable f) => FreeT f m a -> m (Free f a)
```

In our case, we specialize this to:

```haskell
joinFreeT :: (MonadSample m) => FreeT (RecursiveTree Word) m CAT -> m Fragment
```


Amazingly, but somehow not surprisingly, *recursion-schemes* knows that `FreeT` is corecursive, so we can use it in an unfold, and voila, we finally have a way to create trees, tree fragments, (and indeed any other recursive datatype) stochastically:

```haskell
TODO
```

## Step 7: State

We need to make our monad slightly fancier. We want it to not just be a member of `MonadSample`, but also of `MonadState (CAT -> [Fragment])`. This is because we are going to want to be able to get and put fragments to/from the cache, which will be more or less a list of fragments for each value of `CAT`.

## Step 8: a fragment grammar

`fragment` is the core generative process:

```haskell
TODO
```

Here's what this does. At each step of the unfolding, we do as follows: with some probability linked to the number of existing fragments, we decide whether to get a fragment from the cache. If we do get one from the cache, we will use it to continue the unfolding. If not, we will sample a new fragment, use it, and add it to the cache.

## Step 9: visualization

It is pleasing to note that while the creation of a tree involves an unfolding, the transformation of a tree into a visualization is the dual operation, of folding. Naturally, recursion-schemes provides, for every unfolding operation, its dual folding operation.

We create visualizations using the excellent *diagrams* package (actually it's several linked packages). *diagrams* provides a DSL in Haskell for compositionally generating diagrams. 

## Step 10 is inference

The reason we use *monad-bayes* is that if you define something generically in terms of the MonadSample and MonadInfer classes, it provides a range of inference algorithms like MCMC, and methods for customizing your own inference.

In general, we want to ask questions like: given the generative process described by `fragment`, and given a set of observed sentences, what must the set of fragments have been to have resulted in the generation of those sentences.

This is an *extremely* challenging inference problem, and just using MCMC out of the box is beyond hopeless. But as I better understand inference in this domain, I hope to use the tools of monad-bayes to implement something tractable. 

