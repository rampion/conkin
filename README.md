One thing I haven't often seen people talk about doing in Haskell is working with data in [column-major order](https://en.wikipedia.org/wiki/Row-_and_column-major_order), or as a [struct of arrays](https://en.wikipedia.org/wiki/AOS_and_SOA). If we take a look though, there's some interesting possibilities and theory underlying this relatively simple concept.  

The [`conkin` package](http://hackage.haskell.org/package/conkin) is the result of my explorations along this line of thinking.

<!--
# Setup

This is a literate haskell file, so we need to specify all our `LANGUAGE` pragma and imports up front.  But just because we *need* to, doesn't mean we need to show it our reader, thus the HTML comments.

```haskell
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
module Main where
import Data.Functor.Identity (Identity(..))
import Control.Applicative (Alternative(..))
import "conkin" Conkin (type (~>)((~$~)))
import qualified "conkin" Conkin
import Numeric (showHex)
import Data.Char (toUpper)
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Default (Default(..))
import Data.Monoid (All(..), (<>))
import GHC.Generics
import Test.DocTest

main :: IO ()
main = doctest $ words "-pgmL markdown-unlit README.lhs"
```

A couple things only need to be set for the tests.

```haskell
{-$
>>> :set -XTypeApplications -XTypeOperators -XStandaloneDeriving -XDeriveGeneric
-}
```

By using an alternate printer, we get much more legible example results in the doctests

```haskell
{-$
>>> import Text.Show.Pretty (pPrint)
>>> :set -interactive-print pPrint
-}
```

And some custom data types are handy, but could be distracting pedagogically:

```haskell
type Dollars = Double

newtype UPC = UPC { getUPC :: Integer }
  deriving (Num, Eq, Ord)
instance Show UPC where
  showsPrec _ (UPC u) = showString "0x" . (map toUpper (showHex u []) ++)
```
-->

# An example of use

Suppose we have a list of items we wish to manipulate in column-major order:

```haskell
items :: [Item]
items = [ chocolateBar, toiletPaper, ibuprofen ]

chocolateBar, toiletPaper, ibuprofen :: Item

chocolateBar = Item 0xDE1EC7AB1E "chocolate bar" 1.50
toiletPaper = Item 0xDEFEC8 "toilet paper" 9.99
ibuprofen = Item 0x43A1A11 "ibuprofen" 5.25
```

Using the `Functor` instance for lists, we can easily extract each field into its own list:

```haskell
extractFields0 :: [Item] -> ([UPC], [String], [Double])
extractFields0 items = ( upc <$> items, name <$> items, price <$> items )

{-$-----------------------------------------------------------------------------
>>> extractFields0 items
( [ 0xDE1EC7AB1E , 0xDEFEC8 , 0x43A1A11 ]
, [ "chocolate bar" , "toilet paper" , "ibuprofen" ]
, [ 1.5 , 9.99 , 5.25 ]
)
-}
```

We've lost bit of semantic meaning, however, as we've switched from our own custom data type to a generic tuple.  We can regain this meaning if we define a type specifically for a collection of items, parameterized by the collection type:

```haskell
extractFields1 :: [Item] -> ItemF []
extractFields1 items = ItemF (upc <$> items) (name <$> items) (price <$> items)

{-$-----------------------------------------------------------------------------
>>> extractFields1 items
ItemF
  { _upc = [ 0xDE1EC7AB1E , 0xDEFEC8 , 0x43A1A11 ]
  , _name = [ "chocolate bar" , "toilet paper" , "ibuprofen" ]
  , _price = [ 1.5 , 9.99 , 5.25 ]
  }
-}
data ItemF f = ItemF 
  { _upc :: f UPC
  , _name :: f String
  , _price :: f Dollars
  }
deriving instance (Show (f String), Show (f Dollars), Show (f UPC)) => Show (ItemF f)
deriving instance (Eq (f String), Eq (f Dollars), Eq (f UPC)) => Eq (ItemF f)
```

With a little help from `PatternSynonyms` we can derive the `Item` type from `ItemF`, making sure the two definitions don't slip out of step:

```haskell
{-$-----------------------------------------------------------------------------
>>> items
[ ItemF
    { _upc = Identity 0xDE1EC7AB1E
    , _name = Identity "chocolate bar"
    , _price = Identity 1.5
    }
, ItemF
    { _upc = Identity 0xDEFEC8
    , _name = Identity "toilet paper"
    , _price = Identity 9.99
    }
, ItemF
    { _upc = Identity 0x43A1A11
    , _name = Identity "ibuprofen"
    , _price = Identity 5.25
    }
]
-}

-- import Data.Functor.Identity (Identity(..))
-- ...
type Item = ItemF Identity

-- {-# LANGUAGE PatternSynonyms #-}
-- ...
pattern Item :: UPC -> String -> Dollars -> Item
pattern Item upc name price = ItemF (Identity upc) (Identity name) (Identity price) 

upc :: Item -> UPC
upc = runIdentity . _upc

name :: Item -> String
name = runIdentity . _name

price :: Item -> Dollars
price = runIdentity . _price
```

So what else can we do with `ItemF`?  We can't make it a `Functor`, it's got the wrong *kind*. 

```haskell
{-$-----------------------------------------------------------------------------
>>> instance Functor ItemF where fmap = undefined
<BLANKLINE>
... 
    • Expected kind ‘* -> *’, but ‘ItemF’ has kind ‘(* -> *) -> *’
    • In the first argument of ‘Functor’, namely ‘ItemF’
      In the instance declaration for ‘Functor ItemF’
-}
```

But it's still got this parameter that it's covariant and homogenous in - all the fields must use the same container of kind `* -> *`, and changing what container we're using should be easy.

So let's define a different `Functor` class for types of kind `(k -> *) -> *`.

```haskell
{-$-----------------------------------------------------------------------------
>>> :i Conkin.Functor
class Conkin.Functor (f :: (k -> *) -> *) where
  Conkin.fmap :: forall (a :: k -> *) (b :: k -> *).
                 (forall (x :: k). a x -> b x) -> f a -> f b
...
-}

-- import qualified Conkin
-- ...
instance Conkin.Functor ItemF where
  fmap f (ItemF {..}) = ItemF
    { _upc = f _upc
    , _name = f _name
    , _price = f _price
    }
```

Now we can use `Conkin.fmap` to convert an individual `Item` into a `ItemF []`

```haskell
{-$-----------------------------------------------------------------------------
>>> :t Conkin.fmap (\(Identity x) -> [x])
Conkin.fmap (\(Identity x) -> [x])
  :: Conkin.Functor f => f Identity -> f []
>>> Conkin.fmap (\(Identity x) -> [x]) chocolateBar
ItemF
  { _upc = [ 0xDE1EC7AB1E ]
  , _name = [ "chocolate bar" ]
  , _price = [ 1.5 ]
  }
-}
```

We could stitch together multiple of these `ItemF []` into one if `ItemF []` had a `Monoid` instance:

```haskell
extractFields2 :: [Item] -> ItemF []
extractFields2 = foldMap $ Conkin.fmap $ pure . runIdentity

{-$-----------------------------------------------------------------------------
>>> extractFields2 items
ItemF
  { _upc = [ 0xDE1EC7AB1E , 0xDEFEC8 , 0x43A1A11 ]
  , _name = [ "chocolate bar" , "toilet paper" , "ibuprofen" ]
  , _price = [ 1.5 , 9.99 , 5.25 ]
  }
-}

-- import Control.Applicative (Alternative(..))
-- ...
instance Alternative a => Monoid (ItemF a) where
  mempty = ItemF empty empty empty
  left `mappend` right = ItemF
    { _upc = _upc left <|> _upc right
    , _name = _name left <|> _name right
    , _price = _price left <|> _price right
    }
```

Of course we could do this before with `extractFields1`, but there's nothing specific to `ItemF` in the definition of `extractFields2`.  The same definition would work for any `Conkin.Functor` that formed a `Monoid`:

```haskell
{-$-----------------------------------------------------------------------------
>>> :t foldMap $ Conkin.fmap $ pure . runIdentity
foldMap $ Conkin.fmap $ pure . runIdentity
  :: (Applicative b, Conkin.Functor f, Monoid (f b), Foldable t) =>
     t (f Identity) -> f b
-}
```

Another useful monoid is `ItemF Maybe`. This could let us combine multiple partially specified items into one:

```haskell
{-$-----------------------------------------------------------------------------
>>> mempty { _price = Just 2.99 }
ItemF { _upc = Nothing , _name = Nothing , _price = Just 2.99 }
>>> mempty { _price = Just 2.99 } <> mempty { _upc = Just 0x0 }
ItemF { _upc = Just 0x0 , _name = Nothing , _price = Just 2.99 }
-}
```

(Side note - I love being able to partially specify `ItemF Maybe` using `mempty` with record notation.  All the succinctness of `ItemF { _price = Just 2.99 }`, but none of the missing fields.)

We can use `<>` (aka `mappend`) to transform a partially specified item into a fully specified one:

```haskell
withDefaults0 :: ItemF Maybe -> Item
withDefaults0 partial = Conkin.fmap (Identity . fromJust) $ partial <> ItemF
  { _upc = Just 0x0
  , _name = Just "unknown"
  , _price = Just 0
  }

{-$-----------------------------------------------------------------------------
>>> withDefaults0 mempty
ItemF
  { _upc = Identity 0x0
  , _name = Identity "unknown"
  , _price = Identity 0.0
  }
>>> withDefaults0 mempty { _price = Just 2.99, _name = Just "flyswatter" }
ItemF
  { _upc = Identity 0x0
  , _name = Identity "flyswatter"
  , _price = Identity 2.99
  }
-}
```

However, I'm not a big fan of this solution. We've abandoned some safety by using the partial `fromJust`.  If a future developer alters a default to be `Nothing`, the compiler won't complain, we'll just get a runtime error.

What I'd rather be using is the safer `fromMaybe`, but since that's a two-argument function, I can't just use it via `fmap`. I need `ItemF` to be an `Applicative`.

We'll need a slightly different `Applicative` class than `Prelude`'s, as `ItemF` again has the wrong kind:

```haskell
{-$-----------------------------------------------------------------------------
>>> :i Conkin.Applicative
class Conkin.Functor f =>
      Conkin.Applicative (f :: (k -> *) -> *) where
  Conkin.pure :: forall (a :: k -> *). (forall (x :: k). a x) -> f a
  (Conkin.<*>) :: forall (a :: k -> *) (b :: k -> *).
                  f (a ~> b) -> f a -> f b
...
>>> :i (~>)
type role (~>) representational representational nominal
newtype (~>) (a :: k -> *) (b :: k -> *) (x :: k)
  = Conkin.Arrow {(~$~) :: a x -> b x}
...
-}

instance Conkin.Applicative ItemF where
  pure a = ItemF a a a
  ItemF fi fs fd <*> ItemF ai as ad
    = ItemF (fi ~$~ ai) (fs ~$~ as) (fd ~$~ ad)
```

Now we can lift `fromMaybe`:

```haskell
withDefaults1 :: ItemF Maybe -> Item
withDefaults1 = Conkin.liftA2 (\(Identity x) -> Identity . fromMaybe x) ItemF
    { _upc = Identity 0x0
    , _name = Identity "unknown"
    , _price = Identity 0
    }

{-$-----------------------------------------------------------------------------
>>> withDefaults1 mempty
ItemF
  { _upc = Identity 0x0
  , _name = Identity "unknown"
  , _price = Identity 0.0
  }
>>> withDefaults1 mempty { _price = Just 2.99, _name = Just "flyswatter" }
ItemF
  { _upc = Identity 0x0
  , _name = Identity "flyswatter"
  , _price = Identity 2.99
  }
-}
```

Using `data-default`'s `Default` class, we can generalize this idea to create a function that converts any partially-specified `Conkin.Applicative` to a fully specified one.

```haskell
withDefaults2 :: (Conkin.Applicative f, Default (f Identity)) => f Maybe -> f Identity
withDefaults2 = Conkin.liftA2 (\(Identity x) -> Identity . fromMaybe x) def

instance Default Item where
  def = ItemF
    { _upc = Identity 0x0
    , _name = Identity "unknown"
    , _price = Identity 0
    }

{-$-----------------------------------------------------------------------------
>>> withDefaults2 mempty :: ItemF Identity
ItemF
  { _upc = Identity 0x0
  , _name = Identity "unknown"
  , _price = Identity 0.0
  }
>>> withDefaults2 mempty { _price = Just 2.99, _name = Just "flyswatter" }
ItemF
  { _upc = Identity 0x0
  , _name = Identity "flyswatter"
  , _price = Identity 2.99
  }
-}
```

What also might be nice is a way to test whether a `ItemF Maybe` is actually fully specified:

```haskell
isAllJust :: Conkin.Foldable f => f Maybe -> Bool
isAllJust = getAll . Conkin.foldMap (All . isJust)

{-$-----------------------------------------------------------------------------
>>> isAllJust mempty { _upc = Just 0x1111111111 }
False
>>> isAllJust ItemF { _upc = Just 0xDEADBEEF, _name = Just "hamburger", _price = Just 1.99 }
True
-}
```

At this point, it should not be surprising that we need a slightly different `Foldable` in order to collapse `ItemF` values:

```haskell
{-$-----------------------------------------------------------------------------
>>> :i Conkin.Foldable
class Conkin.Foldable (t :: (k -> *) -> *) where
  Conkin.foldr :: forall (a :: k -> *) b.
                  (forall (x :: k). a x -> b -> b) -> b -> t a -> b
  Conkin.foldMap :: forall m (a :: k -> *).
                    Monoid m =>
                    (forall (x :: k). a x -> m) -> t a -> m
...
-}

instance Conkin.Foldable ItemF where
  foldMap f (ItemF {..}) = f _upc <> f _name <> f _price
```

We could use `isAllJust` to safely create an `Item` from a fully-specified `ItemF Maybe`:

```haskell
toItem0 :: ItemF Maybe -> Maybe Item
toItem0 i | isAllJust i = Just $ Conkin.fmap (Identity . fromJust) i
          | otherwise   = Nothing
```

But the `conkin` package already provides a function that does just that:

```haskell
{-$-----------------------------------------------------------------------------
>>> Conkin.apportion mempty { _upc = Just 0x1111111111 }
Nothing
>>> Conkin.apportion ItemF { _upc = Just 0xDEADBEEF, _name = Just "hamburger", _price = Just 1.99 }
Just
  ItemF
    { _upc = Identity 0xDEADBEEF
    , _name = Identity "hamburger"
    , _price = Identity 1.99
    }
>>> :t Conkin.apportion
Conkin.apportion
  :: (Conkin.Traversable g, Applicative f) => g f -> f (g Identity)
-}
```

Although `conkin` does require that `ItemF` implement its custom `Traversable` class, it provides helpers for tuple-like classes like `ItemF`.

```haskell
{-$-----------------------------------------------------------------------------
>>> :m +Data.Functor.Compose
>>> :i Conkin.Traversable
class (Conkin.Foldable t, Conkin.Functor t) =>
      Conkin.Traversable (t :: (i -> *) -> *) where
  Conkin.traverse :: forall j (f :: (j -> *) -> *) (a :: i
                                                         -> *) (b :: i -> j -> *).
                     Conkin.Applicative f =>
                     (forall (x :: i). a x -> f (b x))
                     -> t a -> f (Compose t (Conkin.Flip b))
  Conkin.sequenceA :: forall j (f :: (j -> *) -> *) (a :: i
                                                          -> j -> *).
                      Conkin.Applicative f =>
                      t (Compose f a) -> f (Compose t (Conkin.Flip a))
...
-}
instance Conkin.Traversable ItemF where
  sequenceA (ItemF {..}) = Conkin.liftT3 ItemF _upc _name _price
```

We could also attempt to use `apportion` to invert `extractFields2`, but it mixes
up the columns:

```haskell
{-$-----------------------------------------------------------------------------
>>> items
[ ItemF
    { _upc = Identity 0xDE1EC7AB1E
    , _name = Identity "chocolate bar"
    , _price = Identity 1.5
    }
, ItemF
    { _upc = Identity 0xDEFEC8
    , _name = Identity "toilet paper"
    , _price = Identity 9.99
    }
, ItemF
    { _upc = Identity 0x43A1A11
    , _name = Identity "ibuprofen"
    , _price = Identity 5.25
    }
]
>>> Conkin.apportion (extractFields2 items)
[ ItemF
    { _upc = Identity 0xDE1EC7AB1E
    , _name = Identity "chocolate bar"
    , _price = Identity 1.5
    }
, ItemF
    { _upc = Identity 0xDE1EC7AB1E
    , _name = Identity "chocolate bar"
    , _price = Identity 9.99
    }
, ItemF
    { _upc = Identity 0xDE1EC7AB1E
    , _name = Identity "chocolate bar"
    , _price = Identity 5.25
    }
...
, ItemF
    { _upc = Identity 0x43A1A11
    , _name = Identity "ibuprofen"
    , _price = Identity 1.5
    }
, ItemF
    { _upc = Identity 0x43A1A11
    , _name = Identity "ibuprofen"
    , _price = Identity 9.99
    }
, ItemF
    { _upc = Identity 0x43A1A11
    , _name = Identity "ibuprofen"
    , _price = Identity 5.25
    }
]
-}
```

This is because of `[]`'s `Applicative` instance. If we use the `ZipList` newtype wrapper, we can get the behaviour we desire:

```haskell
{-$-----------------------------------------------------------------------------
>>> import Control.Applicative (ZipList(..))
>>> Conkin.align (ZipList items)
ItemF
  { _upc =
      ZipList { getZipList = [ 0xDE1EC7AB1E , 0xDEFEC8 , 0x43A1A11 ] }
  , _name =
      ZipList
        { getZipList = [ "chocolate bar" , "toilet paper" , "ibuprofen" ] }
  , _price = ZipList { getZipList = [ 1.5 , 9.99 , 5.25 ] }
  }
>>> Conkin.apportion (Conkin.align (ZipList items))
ZipList
  { getZipList =
      [ ItemF
          { _upc = Identity 0xDE1EC7AB1E
          , _name = Identity "chocolate bar"
          , _price = Identity 1.5
          }
      , ItemF
          { _upc = Identity 0xDEFEC8
          , _name = Identity "toilet paper"
          , _price = Identity 9.99
          }
      , ItemF
          { _upc = Identity 0x43A1A11
          , _name = Identity "ibuprofen"
          , _price = Identity 5.25
          }
      ]
  }
-}
```

Here we use the handy `align` function as yet another way to implement `extractFields`:

```haskell
{-$-----------------------------------------------------------------------------
>>> :t Conkin.align
Conkin.align
  :: (Conkin.Applicative g, Traversable f) => f (g Identity) -> g f
-}
```

# A little bit of theory

Typically in Haskell, we talk about the category *Hask*, where the objects are types of kind `*` and the arrows are normal Haskell functions.  In general, a *functor* is a mapping between categories, mapping each object or arrow in one category to an object or arrow (respectively) in another.

The `Prelude`'s `Functor` typeclass actually describes *endofunctors* from Hask to Hask; given a `Functor f`, we can map any type `a` in `Hask` to the type `f a` in Hask (so `f` must have kind `* -> *`), and we can map any arrow (function) `a -> b` in Hask to an arrow `f a -> f b` in Hask (using `fmap`).

The `conkin` package focuses on the functors from *Hask<sup>k</sup>* to *Hask*. In Hask<sup>k</sup>, the objects are types of kind `k -> *`, and the arrows are transformations `a ~> b` where `(a ~> b) x ~ (a x -> b x)`.  A functor from Hask<sup>k</sup> to Hask must then be able to map any type `a :: k -> *` in Hask<sup>k</sup> to a type `f a :: *` in Hask (so `f` must have kind `(k -> *) -> *`), and must be able to map any arrow `a ~> b` in Hask<sup>k</sup> to an arrow `f a -> f b` in Hask.

(I'm not very well read in category theory, so it's thoroughly possible Hask<sup>k</sup> has a more common name in literature, I just chose that one out of similarity with type exponentials.)

You can lift any functor from Hask to Hask to a functor from Hask<sup>k</sup> to Hask using `Dispose`:

```haskell
{-$-----------------------------------------------------------------------------
>>> :i Conkin.Dispose
type role Conkin.Dispose representational nominal nominal
newtype Conkin.Dispose (f :: * -> *) (x :: k) (a :: k -> *)
  = Conkin.Dispose {Conkin.getDispose :: f (a x)}
...
-}
```

And any functor from Hask<sup>k</sup> to Hask can be lifted to a functor from Hask to Hask using `Coyoneda`:

```haskell
{-$-----------------------------------------------------------------------------
>>> :i Conkin.Coyoneda
type role Conkin.Coyoneda representational representational
data Conkin.Coyoneda (t :: (k -> *) -> *) u where
  Conkin.Coyoneda :: forall k (t :: (k -> *) -> *) u (a :: k -> *).
                     (forall (x :: k). a x -> u) -> (t a) -> Conkin.Coyoneda t u
...
-}
```

Not only do both of these encodings preserve functorality, but they also preserve foldability, applicativity, and traversability (e.g. `Traversable t => Conkin.Traversable (Conkin.Dispose t x)`).

Another interesting facet of functors from Hask<sup>k</sup> to Hask is the similarity between their kind, `(k -> *) -> *`, and the type of continuations, `type Cont r a = (a -> r) -> r`. This **con**tinuation **kin**d is where the `conkin` package gets its name from.  

If we start to look at these functors as types of kind `Cont Type i`, then we can can start thinking of how to compose them 
in an algebra, using

* `Conkin.Product f g :: Cont Type (i,j)` as the product type of functors `f :: Cont Type i` and `g :: Cont Type j`
* `Conkin.Coproduct f g :: Cont Type (Either i j)` as the coproduct type of functors `f :: Cont Type i` and `g :: Cont Type j`

Interestingly, `Conkin.Product f g a` is isomorphic to `f (Compose g a)`, making `Conkin.sequenceA` the equivalent of [`Data.Tuple.swap`](http://hackage.haskell.org/package/base-4.10.0.0/docs/Data-Tuple.html#v:swap).

# Notes and concerns

## Existing Work

The `conkin` package isn't unprecedented. In addition to Edward Kmett's [even more general `categories` package](http://hackage.haskell.org/package/categories), there's also Gracjan Polak's [`fieldwise` package](http://hackage.haskell.org/package/fieldwise), which supports a similar set of operations for types of kind `(k -> *) -> *`.

## Boilerplate instances

Instances of `Conkin`'s `Functor`, `Applicative`, `Foldable`, and `Traversable` classes are mainly mechanical, and seem like excellent candidates for using `-XDeriveGeneric` and `-XDefaultSignatures` to reduce the amount of boilerplate needed for use.  This is not currently true, as you cannot encode a type like `ItemF` using the fundamental representational types GHC knows about:

```haskell
{-$-----------------------------------------------------------------------------
>>> deriving instance Generic1 (ItemF)
...
    • Can't make a derived instance of ‘Generic1 ItemF’:
        Constructor ‘ItemF’ applies a type to an argument involving the last parameter
                            but the applied type is not of kind * -> *, and
        Constructor ‘ItemF’ applies a type to an argument involving the last parameter
                            but the applied type is not of kind * -> *, and
        Constructor ‘ItemF’ applies a type to an argument involving the last parameter
                            but the applied type is not of kind * -> *
    • In the stand-alone deriving instance for ‘Generic1 (ItemF)’
-}
```

It's very possible to hand-write instances of `Generic1` for functors from Hask<sup>k</sup> to Hask 
using an fundamental representational type, `Par2`:

```haskell
newtype Par2 (x :: k) (a :: k -> *) = Par2 { unPar2 :: a x }

instance Generic1 ItemF where
  type Rep1 ItemF =
    D1 ('MetaData "ItemF" "Main" "conkin" 'True)
      (C1 ('MetaCons "ItemF" 'PrefixI 'True)
        (S1 ('MetaSel ('Just "_upc") 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
          (Par2 UPC)
         :*:
         S1 ('MetaSel ('Just "_name") 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
          (Par2 String)
         :*:
         S1 ('MetaSel ('Just "_cost") 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
          (Par2 Dollars)))
  from1 (ItemF {..}) = M1 (M1 (M1 (Par2 _upc) :*: M1 (Par2 _name) :*: M1 (Par2 _price)))
  to1 (M1 (M1 (M1 (Par2 _upc) :*: M1 (Par2 _name) :*: M1 (Par2 _price)))) = ItemF {..}
```

However the verbosity of the above makes it less useful as a way to avoid boilerplate.

This is not necessarily the end of all hope; I could make a pull request to GHC including `Par2` and updates to the `DeriveGeneric` mechanism, or write some `TemplateHaskell` macros to generate the instances.  Until I do so, I've gone the fairly low-effort route of providing a few helper functions to make `Conkin.Traversable` instances easier to write.

## Use of `unsafeCoerce`

In my personal Haskell experience, my only uses of `unsafeCoerce` until this package had been for `newtype` wrappers and such (i.e. excellent candidates to use `coerce` instead).  This library marks the first time I found myself using `unsafeCoerce` because I just couldn't think of another way to convince the compiler of something, in `Dispose`'s implementation of `Conkin.Traversable`:

```
instance Prelude.Traversable t => Traversable (Dispose t x) where
  sequenceA = teardown . Prelude.traverse setup . getDispose where
    setup :: Compose f a x -> Coyoneda f (Exists (a x))
    setup = Coyoneda Exists . getCompose

    teardown :: (Functor f, Prelude.Functor t) => Coyoneda f (t (Exists (a x))) -> f (Compose (Dispose t x) (Flip a))
    teardown (Coyoneda k fax) = Compose . Dispose . Prelude.fmap Flip . unwrap k <$> fax

    -- by parametricity, `t`'s implementation of `Prelude.sequenceA :: t (g e) ->
    -- g (t e)` can't inspect the value of `e`, so all `Exists a` values
    -- must be wrapped `a x` values, so this should be an okay use
    -- of `unsafeGetExists`.
    unwrap :: Prelude.Functor t => (b x -> t (Exists a)) -> b x -> t (a x)
    unwrap k bx = Prelude.fmap (unsafeGetExists bx) $ k bx

    unsafeGetExists :: proxy x -> Exists a -> a x
    unsafeGetExists _ (Exists az) = unsafeCoerce az

data Exists (a :: k -> *) where
  Exists :: a x -> Exists a
```

I've managed to convince myself that my use of `unsafeCoerce` is, well, safe, but only until someone finds a law-abiding `Traversable` that proves me wrong.  I should probably come back to this, and either come up with a more formal proof of validity, rather than the loose argument I present in the code.
  
# Literate Haskell

This `README.md` file is a literate haskell file, for use with [`markdown-unlit`](https://github.com/sol/markdown-unlit#readme).  To allow GHC to recognize it, it's softlinked as `README.lhs`, which you can compile with

    $ ghc -pgmL markdown-unlit README.lhs

Many of the above examples are [`doctest`](https://github.com/sol/doctest#readme)-compatible, and can be run with

    $ doctest -pgmL markdown-unlit README.lhs

Alternately, you can have cabal manage the dependencies and compile and test this with:

    $ cabal install happy
    $ cabal install --enable-tests
    $ cabal test readme
