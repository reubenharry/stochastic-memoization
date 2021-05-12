UNDER CONSTRUCTION

# Stochastic Memoization

TODO: diagram

What you see here is a sequence of trees which have been probabilistically generated. In the process of generating them, a number of "fragments", or partially complete trees, have been stored and reused. These are shown in the red box at the bottom of the diagram
TODO.

Haskell's powerful tools for expressing rich but principled patterns of recursion, especially when this recursion interacts with side-effects (global state, randomness), are a perfect fit for this problem.


# To run

Download the Haskell Stack tool. Do:

stack build

stack ghci

This second command will open a repl, in which you can write "makeDiagram" to generate sentences and corresponding diagrams

# Docs

The core functionality of the library is in `makeFragment` which probabilistically generates trees while stochastically caching tree fragments. This is complicated, so I'll build up to it step by step. (I'm assuming that the reader is familiar with Haskell at an intermediate level.)

## Step 1: The datatype

```haskell
data NonRecursiveTree a x =
  Leaf a
  | Branch x x
```

As the name suggests, this type is not recursive; it's just one tree layer. `a` is the type of a leaf, and `x` is the type of each branch.

The type of a full tree is then:

```haskell
type RecursiveTree a = NonRecursiveTree a (RecursiveTree a)
```

Or more succintly:

```haskell
type RecursiveTree a = Fix (NonRecursiveTree a)
```

Note the recursion. This type isn't actually going to feature in the code, because we're going to use the excellent *recursion-schemes* package, which will make use of the non-recursive type instead. As it nicely states in the recursion-scheme docs: "The core idea of this library is that instead of writing recursive functions on a recursive datatype, we prefer to write non-recursive functions on a related, non-recursive datatype we call the "base functor"."

In our case, the "base functor" is `NonRecursiveTree String`, and the recursive type is `RecursiveTree`.

## Step 2: unfolding a tree

What's particularly nice about *recursion-schemes* is its generality. The function `unfold` has type:

```haskell
unfold :: Corecursive t => (a -> Base t a) -> a -> t
```

This expresses what it means to unfold not just a binary branching tree, but in fact any kind of (co)recursive structure. This will prove particularly useful. What will also prove useful is that in addition to `unfold`, a few other, richer patterns of unfolding are supplied, and as we'll see, these are precisely what we need.

We want to make a tree of type `RecursiveTree String`, by starting with a seed. Let's say that the seed is of type `CAT` (for "category"), defined as:

```haskell
data CAT = S' | NP' | VP' | A' | N' | DET' | COP' | V'
```

Then we can make the tree as follows:

```haskell
simpleTree = unfold induction TODO
TODO
```

## Step 3: tree fragments

What we have now is not very useful though: the tree that gets output is always the same, and no tree fragments are stored. Let's deal with the issue of fragments first. To do this, we introduce a new recursive type:


```haskell
type Fragment = Free (NonRecursiveTree String) CAT

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

Now, as mentioned, `unfold` in *recursion-schemes* is delightfully general, and so knows that `Free f a` is something which you can make with an `unfold`.


```haskell
TODO
```

## Step 4: unfold a tree using fragments

The next order of business (step 4) is to generate whole trees, but to use fragments in the process. That is, at a given node, rather than proceeding with a left branch and a right branch, we have the option of sticking in a fragment. This diagram illustrates the idea:

TODO

How to do this? It turns out that Data.Functor.Foldable has some other unfolding patterns which are fancier than `unfold`, and these are just what we need. First there's `apo`, which allows you to stick in fully complete trees at a given node. But we want to next, fancier, thing: `futu`: 


```haskell
futu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
```

Or specializing this to our use case, (t = RecursiveTree String):

```haskell
futu :: (CAT -> NonRecursiveTree String Fragment) -> CAT -> RecursiveTree String
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

`FreeT m (NonRecursiveTree String) CAT` is precisely a tree, or fragment of a tree, where each succesive layer is wrapped in a new layer of the monad `m`. A very handy function provided by the *free* package is `joinFreeT`:

```haskell
joinFreeT :: (Monad m, Traversable f) => FreeT f m a -> m (Free f a)
```

In our case, we specialize this to:

```haskell
joinFreeT :: (MonadSample m) => FreeT (RecursiveTree String) m CAT -> m Fragment
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

