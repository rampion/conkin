Recently I found myself considering how the [Array of Structures (AoS) and Structure of Arrays (SoA) layouts](https://en.wikipedia.org/wiki/AOS_and_SOA) would translate in modern Haskell.

```haskell
{-# LANGUAGE RankNTypes #-}
module README where
import Control.Applicative
import Data.Functor.Identity
```

The AoS layout is conventional enough - you have a list (or vector) of simple data:

```haskell
data X
data Y
data Z
data Struct = Struct X Y Z
type ListOfStruct = [Struct]
```

The SoA layout turns that on its head, creating a new structure that has lists
of all the fields in the original data structure:

```haskell
data StructOfList = StructOfList [X] [Y] [Z]
```

Converting one to another is easy enough:

```haskell
toListOfStruct :: StructOfList -> ListOfStruct
toListOfStruct (StructOfList xs ys zs) = zipWith3 Struct xs ys zs

toStructOfList :: ListOfStruct -> StructOfList
toStructOfList = foldr cons nil where
  nil = StructOfList [] [] []
  cons (Struct x y z) (StructOfList xs ys zs) = StructOfList (x:xs) (y:ys) (z:zs)
```

But there's a lot of structure repeated between `Struct` and `StructOfList`.  Parameterization to the rescue!

```haskell
data StructF a = StructF (a X) (a Y) (a Z)
type Struct' = StructF Identity
```

This parameterization has opened up some possibilities. Now we can convert between `StructF a` and `a Struct'` for any `Applicative a`:

```haskell
fromStructF :: Applicative a => StructF a -> a Struct'
fromStructF (StructF ax ay az) = liftA3 rec' ax ay az where
  rec' x y z = StructF (Identity x) (Identity y) (Identity z)

toStructF :: Functor a => a Struct' -> StructF a
toStructF ar = StructF ax ay az where
  ax = ar <&> \(StructF (Identity x) _ _) -> x
  ay = ar <&> \(StructF _ (Identity y) _) -> y
  az = ar <&> \(StructF _ _ (Identity z)) -> z
  (<&>) = flip (<$>)
```

Though this suggests we should be using `ZipList` instead of `[]`:

```haskell
type ListOfStruct' = ZipList Struct'
type StructOfList' = StructF ZipList
```

`StructF` also has the ability to change its container:

```haskell
mapStructF :: (forall t. a t -> b t) -> StructF a -> StructF b
mapStructF f (StructF ax ay az) = StructF (f ax) (f ay) (f az)
```

Taking a step back, we can see that `StructF` and `mapStructF` are acting like a *functor*, in the category theory sense of the word:
- `StructF` converts types of kind `* -> *` to types of kind `*`
- `mapStructF` converts arrows between types of kind `* -> *`
  into arrows between types of kind `*`.

Furthermore, this is going to be true of any data type that can convert between SoA and AoS formats.

Consider the category Hask:
- its objects are types of kind `*`
- its arrows are functions `a -> b`.

We can also define category Hask<sup>k</sup>:
- its objects are types of kind `k -> *` for some `k`
- its arrows `a ~> b` are functions `a x -> b x`

A functor `f` from Hask<sup>k</sup> to Hask:
- lifts objects from Hask<sup>k</sup> to Hask, so `f :: (k -> *) -> *`
- lifts arrows from Hask<sup>k</sup> to Hask, so it must define
  `fmap :: (forall x. a x -> b x) -> f a -> f b`

Looking closer at the kind of o

- array of structs (AoS) / struct of arrays (SoA)

- category Hask<sup>k</sup> where 
  - an object `a` is a parameterized type `a :: k -> *`
  - an arrow `a ~> b` is a transformations `a ~> b ~ forall (x :: k). a x -> b x`

- a functor `f` from Hask<sup>k</sup> to Hask 
  - `f :: (k -> *) -> *`
  - `fmap :: (forall (x :: k). a x -> b x) -> f a -> b a`

- the kind `(k -> *) -> *` closely resembles the type
  of continuations `(a -> r) -> r`, which suggests there
  should be a bind `((k -> *) -> *) -> (k -> (j -> *) -> *) -> (j -> *) -> *`
  
# Literate Haskell

This README.md file is a literate haskell file, for use with [`markdown-unlit`](https://github.com/sol/markdown-unlit#readme).
To allow GHC to recognize it, it's softlinked as `README.lhs`, which you can compile with

    $ ghc -pgmL markdown-unlit README.lhs

Many of the above examples are [`doctest`](https://github.com/sol/doctest#readme)-compatible, and can be run with

    $ doctest -pgmL markdown-unlit README.lhs

Alternately, you can have cabal manage the dependencies and compile and test this with:

    $ cabal install --dependencies-only --enable-tests
    $ cabal build
    $ cabal test
