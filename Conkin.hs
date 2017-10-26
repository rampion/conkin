{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | 
-- The 'Conkin' module defines tools for types of kind @(k -> *) -> *@
-- (__con__tinuation __kin__d types), treating them as functors from the category of
-- types of kind @k -> *@ (/Hask^k/) to the category of types of kind @*@ (/Hask/).
--
-- It defines its own 'Functor', 'Applicative', 'Foldable', and 'Traversable'
-- classes, as continuation kind types are kind-incompatible with the
-- homonymous classes in "Prelude".
--
-- The 'Dispose' type lifts a traditional functor to a continuation kind
-- functor:
--
-- >>> :k Dispose Maybe 0
-- Dispose Maybe 0 :: (Nat -> *) -> *
--
-- While the 'Coyoneda' type does the opposite.
--
-- >>> data OfSymbol a = OfSymbol (a "hello")
-- >>> :k OfSymbol
-- OfSymbol :: (Symbol -> *) -> *
-- >>> :k Coyoneda OfSymbol
-- Coyoneda OfSymbol :: * -> *
--
-- Two of the most useful functions provided by the module are 'align' and
-- 'apportion', as they allow you to transpose the composition of a traditional
-- endofunctor and a continuation kind functor.
--
-- >>> rows = zipWith (\ch ix -> Pair (Identity ch, Identity ix)) "abc" [0..2]
-- >>> rows
-- [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 2 ) }
-- ]
-- >>> cols = align rows
-- >>> cols
-- Pair { getPair = ( "abc" , [ 0 , 1 , 2 ] ) }
-- >>> apportion cols
-- [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'a' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'a' , Identity 2 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 2 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 2 ) }
-- ]
-- >>> apportion $ fmap ZipList cols
-- ZipList
--   { getZipList = 
--       [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
--       , Pair { getPair = ( Identity 'b' , Identity 1 ) }
--       , Pair { getPair = ( Identity 'c' , Identity 2 ) }
--       ]
--   }
--
-- There's also convenience types for 'Product's and 'Coproduct's of
-- continuation kind functors, as well as for 'Tuple's and 'Tagged' unions
-- of arbitrary types.
module Conkin 
  {- classes -}
  ( Functor(..), (<$>)
  , Applicative(..), type (~>)(..), liftA2, liftA3, liftA4
  , Foldable(..)
  , Traversable(..), traverse', sequenceA', liftT1, liftT2, liftT3, liftT4, align, apportion
  {- wrappers -}
  , Dispose(..)
  , Coyoneda(..), getCoyoneda, toCoyoneda
  {- functors -}
  , Product(..), toProduct, fromProduct
  , Coproduct(..)
  , Pair(..)
  , Tuple(..)
  , Tagged(..)
  {- utility types -}
  , Flip(..)
  , Curry(..)
  , Uncurry(..), pattern UncurryStrict, getUncurryStrict, uncurried
  , Pure(..)
  --, Exists(..)
  --, Both(..)
  --, Curry2(..)
  --, Compose2(..)
  ) where
import Prelude hiding (Functor(..), (<$>), Applicative(..), Traversable(..), Foldable(..) )
import qualified Prelude
import qualified Control.Applicative as Prelude
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Monoid (Endo(..), (<>))
import Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Identity (Identity(..))

-- $setup
-- >>> :set -XDataKinds -XGADTs
-- >>> :m +GHC.TypeLits
-- >>> import Text.Show.Pretty (pPrint)
-- >>> :set -interactive-print pPrint
-- >>> import Control.Applicative (ZipList(..))

{- Classes ----------------------------------------------------------------------}

-- | A functor from /Hask^k/ to /Hask/, an analogue of 'Prelude.Functor' for kind @(k -> *) -> *@
class Functor (f :: (k -> *) -> *) where
  fmap :: (forall (x :: k). a x -> b x) -> f a -> f b

-- | An analogue of 'Prelude.<$>' for use with "Conkin"'s 'Functor'
(<$>) :: Functor f => (forall x. a x -> b x) -> f a -> f b 
(<$>) = fmap
infixl 4 <$>

-- | An analogue of 'Prelude.Applicative' for kind @(k -> *) -> *@
class Functor f => Applicative (f :: (k -> *) -> *) where
  pure :: (forall (x :: k). a x) -> f a
  (<*>) :: f (a ~> b) -> f a -> f b
infixl 4 <*>

-- | arrows in /Hask^k/ have type @a ~> b :: k -> *@ 
newtype (~>) (a :: k -> *) (b :: k -> *) (x :: k) =
  Arrow { (~$~) :: a x -> b x }
infixr 0 ~>
infixr 0 ~$~
-- XXX: (Prelude.Contravariant a, Prelude.Functor b) => Prelude.Functor (a ~> b)

-- | An analogue of 'Prelude.liftA2' for use with "Conkin"'s 'Applicative'
liftA2 :: Applicative f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
liftA2 f a b = (Arrow . f) <$> a <*> b

-- | An analogue of 'Prelude.liftA3' for use with "Conkin"'s 'Applicative'
liftA3 :: Applicative f => (forall x. a x -> b x -> c x -> d x) -> f a -> f b -> f c -> f d
liftA3 f a b c = Arrow . (Arrow .) . f <$> a <*> b <*> c

-- | An extension of 'liftA3' to functions of four arguments
liftA4 :: Applicative f => (forall x. a x -> b x -> c x -> d x -> e x) -> f a -> f b -> f c -> f d -> f e
liftA4 f a b c d = Arrow . (Arrow .) . ((Arrow.).) . f <$> a <*> b <*> c <*> d

-- | An analogue of 'Prelude.Foldable' for kind @(k -> *) -> *@
class Foldable (t :: (k -> *) -> *) where
  foldr :: (forall (x :: k). a x -> b -> b ) -> b -> t a -> b
  foldr f b ta = foldMap (Endo . f) ta `appEndo` b

  foldMap :: Monoid m => (forall (x :: k). a x -> m) -> t a -> m
  foldMap f = foldr (\ax b -> f ax <> b) mempty

  {-# MINIMAL foldr | foldMap #-}

-- | An analogue of 'Prelude.Traversable' for kind @(k -> *) -> *@
class (Foldable t, Functor t) => Traversable (t :: (i -> *) -> *) where
  traverse :: Applicative f => (forall x. a x -> f (b x)) -> t a -> f (Compose t (Flip b))
  traverse f = sequenceA . fmap (Compose . f)

  sequenceA :: Applicative f => t (Compose f a) -> f (Compose t (Flip a))
  sequenceA = traverse getCompose

  {-# MINIMAL traverse | sequenceA #-}

-- | version of 'traverse' that unflips the inner type 
traverse' :: (Traversable t, Applicative f) => (forall x. a x -> f (Flip b x)) -> t a -> f (Compose t b)
traverse' f = fmap (Compose . fmap (getFlip . getFlip) . getCompose) . traverse f

-- | version of 'sequenceA' that unflips the inner type 
sequenceA' :: (Traversable t, Applicative f) => t (Compose f (Flip a)) -> f (Compose t a)
sequenceA' = fmap (Compose . fmap (getFlip . getFlip) . getCompose) . sequenceA

-- | 'sequenceA' helper for single-parameter constructors
--
-- >>> :{
-- data OfOne a = OfOne (a Int)
-- instance Functor OfOne where
--   fmap h (OfOne a) = OfOne (h a)
-- instance Applicative OfOne where
--   pure = OfOne
--   OfOne f <*> OfOne a = OfOne (f ~$~ a)
-- instance Foldable OfOne where
--   foldMap h (OfOne a) = h a
-- instance Traversable OfOne where
--   sequenceA (OfOne fa) = liftT1 OfOne fa
-- :}
liftT1 :: Applicative g =>
  (forall h. h w -> f h) -> Compose g a w -> g (Compose f (Flip a))
liftT1 c = fmap (Compose . c . Flip) . getCompose

-- | 'sequenceA' helper for two-parameter constructors
--
-- >>> :{
-- data OfTwo a = OfTwo (a Int) (a Char)
-- instance Functor OfTwo where
--   fmap h (OfTwo ai ac) = OfTwo (h ai) (h ac)
-- instance Applicative OfTwo where
--   pure a = OfTwo a a
--   OfTwo fi fc <*> OfTwo ai ac = OfTwo (fi ~$~ ai) (fc ~$~ ac)
-- instance Foldable OfTwo where
--   foldMap h (OfTwo ai ac) = h ai <> h ac
-- instance Traversable OfTwo where
--   sequenceA (OfTwo fai fac) = liftT2 OfTwo fai fac
-- :}
liftT2 :: Applicative g => 
  (forall h. h w -> h x -> f h) -> Compose g a w -> Compose g a x -> g (Compose f (Flip a))
liftT2 c (Compose gaw) (Compose gax) = 
  liftA2 (\awt axt -> Compose $ c (Flip awt) (Flip axt)) gaw gax

-- | 'sequenceA' helper for three-parameter constructors
--
-- >>> :{
-- data OfThree a = OfThree (a Int) (a Char) (a Bool)
-- instance Functor OfThree where
--   fmap h (OfThree ai ac ab) = OfThree (h ai) (h ac) (h ab)
-- instance Applicative OfThree where
--   pure a = OfThree a a a
--   OfThree fi fc fb <*> OfThree ai ac ab = OfThree (fi ~$~ ai) (fc ~$~ ac) (fb ~$~ ab)
-- instance Foldable OfThree where
--   foldMap h (OfThree ai ac ab) = h ai <> h ac <> h ab
-- instance Traversable OfThree where
--   sequenceA (OfThree fai fac fab) = liftT3 OfThree fai fac fab
-- :}
liftT3 :: Applicative g => 
  (forall h. h w -> h x -> h y -> f h) -> Compose g a w -> Compose g a x -> Compose g a y -> g (Compose f (Flip a))
liftT3 c (Compose gaw) (Compose gax) (Compose gay) = 
  liftA3 (\awt axt ayt -> Compose $ c (Flip awt) (Flip axt) (Flip ayt)) gaw gax gay

-- | 'sequenceA' helper for four-parameter constructors
--
-- >>> :{
-- data OfFour a = OfFour (a Int) (a Char) (a Bool) (a Double)
-- instance Functor OfFour where
--   fmap h (OfFour ai ac ab ad) = OfFour (h ai) (h ac) (h ab) (h ad)
-- instance Applicative OfFour where
--   pure a = OfFour a a a a
--   OfFour fi fc fb fd <*> OfFour ai ac ab ad = OfFour (fi ~$~ ai) (fc ~$~ ac) (fb ~$~ ab) (fd ~$~ ad)
-- instance Foldable OfFour where
--   foldMap h (OfFour ai ac ab ad) = h ai <> h ac <> h ab <> h ad
-- instance Traversable OfFour where
--   sequenceA (OfFour fai fac fab fad) = liftT4 OfFour fai fac fab fad
-- :}
liftT4 :: Applicative g => 
  (forall h. h w -> h x -> h y -> h z -> f h) -> Compose g a w -> Compose g a x -> Compose g a y -> Compose g a z -> g (Compose f (Flip a))
liftT4 c (Compose gaw) (Compose gax) (Compose gay) (Compose gaz) = 
  liftA4 (\awt axt ayt azt -> Compose $ c (Flip awt) (Flip axt) (Flip ayt) (Flip azt)) gaw gax gay gaz

-- | Loosely, 'align' transforms an array of structures into a structure
-- of arrays, if by \"array\" one means an arbitrary collection type.
--
-- >>> rows = zipWith (\ch ix -> Pair (Identity ch, Identity ix)) "abc" [0..2]
-- >>> rows
-- [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 2 ) }
-- ]
-- >>> align rows
-- Pair { getPair = ( "abc" , [ 0 , 1 , 2 ] ) }
align :: (Prelude.Traversable f, Applicative g) => f (g Identity) -> g f
align = fmap teardown . sequenceA . Dispose . Prelude.fmap setup where
  setup :: Functor g => g Identity -> Compose g (Flip Const) void
  setup = Compose . fmap (Flip . Const . runIdentity)

  teardown :: Prelude.Functor f => Compose (Dispose f void) (Flip (Flip Const)) x -> f x
  teardown = Prelude.fmap (getConst . getFlip . getFlip) . getDispose . getCompose

-- | Loosely, 'apportion' transforms a structure of arrays into an array
-- of structures, if by \"array\" one means an arbitrary collection type.
--
-- Depending on the collection's 'Prelude.Applicative' instance, this
-- may or may not be the inverse of 'align'.
--
-- >>> cols = Pair { getPair = ( "abc" , [ 0 , 1 , 2 ] ) }
-- >>> apportion cols
-- [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'a' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'a' , Identity 2 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'b' , Identity 2 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 0 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 1 ) }
-- , Pair { getPair = ( Identity 'c' , Identity 2 ) }
-- ]
-- >>> apportion $ fmap ZipList cols
-- ZipList
--   { getZipList = 
--       [ Pair { getPair = ( Identity 'a' , Identity 0 ) }
--       , Pair { getPair = ( Identity 'b' , Identity 1 ) }
--       , Pair { getPair = ( Identity 'c' , Identity 2 ) }
--       ]
--   }
apportion :: (Prelude.Applicative f, Traversable g) => g f -> f (g Identity)
apportion = Prelude.fmap teardown . getDispose . traverse setup where
  setup :: Prelude.Functor f => f x -> Dispose f void (Const x)
  setup = Dispose . Prelude.fmap Const

  teardown :: Functor g => Compose g (Flip Const) void -> g Identity
  teardown = fmap (Identity . getConst . getFlip) . getCompose


{- Dispose -----------------------------------------------------------------------}

-- | If @f@ is a functor from /Hask/ to /Hask/, then,  @forall (x :: k). Dispose f
-- x@ is a functor from /Hask^k/ to /Hask/
--
-- The name comes from the isomorphism @Dispose f ~ Flip (Compose f) :: k -> (k
-- -> *) -> *@, as a pun off the latin prefixes "com-", meaning together, and
-- "dis-", meaning apart.
newtype Dispose (f :: * -> *) (x :: k) (a :: k -> *) =
  Dispose { getDispose :: f (a x) }
  deriving (Show, Eq, Ord)

instance Prelude.Functor f => Functor (Dispose f x) where
  fmap f (Dispose fx) = Dispose $ Prelude.fmap f fx
  
instance Prelude.Applicative f => Applicative (Dispose f x) where
  pure a = Dispose $ Prelude.pure a
  Dispose ff <*> Dispose fa = Dispose $ Prelude.liftA2 (~$~) ff fa

instance Prelude.Foldable t => Foldable (Dispose t x) where
  foldr f b = Prelude.foldr f b . getDispose
  foldMap f = Prelude.foldMap f . getDispose

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


{- Coyoneda ---------------------------------------------------------------------}

-- | If @t@ is a functor from /Hask^k/ to /Hask/, then @Coyoneda t@ is a functor
-- from /Hask/ to /Hask/.
--
-- It's very similar to the 'Data.Functor.Coyoneda.Coyoneda' from the @kan-extensions@ package,
-- differing only in kind, and @Coyoneda t a@ is isomorphic to @t (Const a)@ for any 'Functor'.
data Coyoneda (t :: (k -> *) -> *) (u :: *) where
  Coyoneda :: (forall x. a x -> u) -> t a -> Coyoneda t u

-- | convert a functor from its 'Coyoneda' representation
getCoyoneda :: Functor t => Coyoneda t a -> t (Const a)
getCoyoneda (Coyoneda f t) = Const . f <$> t

-- | convert a functor to its 'Coyoneda' representation
toCoyoneda :: t (Const a) -> Coyoneda t a
toCoyoneda = Coyoneda getConst

instance Prelude.Functor (Coyoneda t) where
  fmap f (Coyoneda k t) = Coyoneda (f . k) t

instance Applicative t => Prelude.Applicative (Coyoneda t) where
  pure a = toCoyoneda $ pure $ Const a

  Coyoneda kf tu <*> Coyoneda ka tv = Coyoneda (k kf ka) (t tu tv) where
    k :: (forall x. u x -> a -> b) -> (forall x. v x -> a) -> (forall x. Both u v x -> b)
    k kf ka (Both (ux, vx)) = kf ux $ ka vx

    t :: Applicative t => t u -> t v -> t (Both u v)
    t = liftA2 $ curry Both

newtype Both (a :: k -> *) (b :: k -> *) (x :: k) = Both (a x, b x)
  -- XXX: Both (Compose f 'Left) (Compose g 'Right) ~ Coproduct f g

instance Foldable t => Prelude.Foldable (Coyoneda t) where
  foldr f b (Coyoneda k t) = foldr (f . k) b t
  foldMap f (Coyoneda k t) = foldMap (f . k) t

instance Traversable t => Prelude.Traversable (Coyoneda t) where
  sequenceA (Coyoneda k t) = Prelude.fmap teardown . getDispose . sequenceA $ setup . k <$> t where
    setup :: Prelude.Functor f => f a -> Compose (Dispose f y) (Curry (Const a)) x
    setup = Compose . Dispose . Prelude.fmap (Curry . Const)

    teardown :: Functor t => Compose t (Flip (Curry (Const a))) y -> Coyoneda t a
    teardown = Coyoneda (getConst . getCurry . getFlip) . getCompose

{- Product ----------------------------------------------------------------------}

-- | The product of two continuation kind functors is a continuation kind functor.
--
-- >>> data A z where A :: Int -> [x] -> [y] -> A '(x,y)
-- >>> data B z where B :: [(x,y)] -> B '(x,y)
-- >>> foo = Product . Pure . Compose . Pure . Curry $ A 0 "abc" [True, False]
-- >>> :t foo
-- foo :: Product (Pure Char) (Pure Bool) A
-- >>> a2b :: A z -> B z ; a2b (A _ xs ys) = B $ zip xs ys 
-- >>> :t fmap a2b foo
-- fmap a2b foo :: Product (Pure Char) (Pure Bool) B
--
newtype Product (f :: (i -> *) -> *) (g :: (j -> *) -> *) (a :: (i,j) -> *) =
  Product { getProduct :: f (Compose g (Curry a)) }

-- | helper to make a 'Product' when the inner type is already curried.
--
-- >>> comma = Pure . Compose . Pure $ ('a', True)
-- >>> :t comma
-- comma :: Pure Char (Compose (Pure Bool) (,))
-- >>> :t toProduct UncurryStrict comma
-- toProduct UncurryStrict comma
--   :: Product (Pure Char) (Pure Bool) (Uncurry (,))
toProduct :: (Functor f, Functor g) => (forall x y. a x y -> b '(x,y)) -> f (Compose g a) -> Product f g b
toProduct f = Product . fmap (Compose . fmap (Curry . f) . getCompose)

-- | helper to unwrap a 'Product' when the inner type is already curried.
--
-- >>> comma' = toProduct UncurryStrict . Pure . Compose . Pure $ ('a', True)
-- >>> :t comma'
-- comma' :: Product (Pure Char) (Pure Bool) (Uncurry (,))
-- >>> :t getProduct comma'
-- getProduct comma'
--   :: Pure Char (Compose (Pure Bool) (Curry (Uncurry (,))))
-- >>> :t fromProduct getUncurryStrict comma'
-- fromProduct getUncurryStrict comma'
--   :: Pure Char (Compose (Pure Bool) (,))
fromProduct :: (Functor f, Functor g) => (forall x y. b '(x,y) -> a x y) -> Product f g b -> f (Compose g a)
fromProduct f =  fmap (Compose . fmap (f . getCurry) . getCompose) . getProduct

deriving instance Show (f (Compose g (Curry a))) => Show (Product f g a)
deriving instance Eq (f (Compose g (Curry a))) => Eq (Product f g a)
deriving instance Ord (f (Compose g (Curry a))) => Ord (Product f g a)

instance (Functor f, Functor g) => Functor (Product f g) where
  fmap h = Product . fmap (Compose . fmap (Curry . h . getCurry) . getCompose) . getProduct

instance (Applicative f, Applicative g) => Applicative (Product f g) where
  pure a = Product $ pure $ Compose $ pure $ Curry a
  Product ff <*> Product fa = Product $ liftA2 (\(Compose gf) (Compose ga) -> Compose $ liftA2 (\(Curry f) (Curry a) -> Curry $ f ~$~ a) gf ga) ff fa

instance (Foldable f, Foldable g) => Foldable (Product f g) where
  foldMap h = foldMap (foldMap (h . getCurry) . getCompose) . getProduct

instance (Traversable f, Traversable g) => Traversable (Product f g) where
  sequenceA = fmap cleanup . traverse setup . getProduct where
    setup :: (Applicative h, Traversable g) => Compose g (Curry (Compose h a)) x -> h (Compose2 (Compose2 (Compose g) Flip) (Curry2 a) x)
    setup = fmap (Compose2 . Compose2) . traverse inner . getCompose

    inner :: Functor h => Curry (Compose h a) x y -> h (Curry2 a x y)
    inner = fmap Curry2 . getCompose . getCurry

    cleanup :: (Functor f, Functor g) => Compose f (Flip (Compose2 (Compose2 (Compose g) Flip) (Curry2 a))) z -> Compose (Product f g) (Flip a) z
    cleanup = Compose . Product . fmap (Compose . fmap (Curry . Flip . getCurry2 . getFlip) . getCompose . getCompose2 . getCompose2 . getFlip) . getCompose

newtype Curry2 (a :: (i,j) -> k -> *) (x :: i) (y :: j) (z :: k) = Curry2 { getCurry2 :: a '(x,y) z }

{- Coproduct --------------------------------------------------------------------}

-- | The coproduct of two continuation kind functors is a continuation kind functor.
--
-- >>> data A z where { AL :: i -> A ('Left i) ; AR :: j -> A ('Right j) }
-- >>> data B z where { BL :: i -> i -> B ('Left i) ; BR :: B ('Right j) }
-- >>> bar = Coproduct (Pure . Compose $ AL True, Pure . Compose $ AR 'a')
-- >>> :t bar
-- bar :: Coproduct (Pure Bool) (Pure Char) A
-- >>> a2b :: A z -> B z ; a2b (AL i) = BL i i ; a2b (AR _) = BR
-- >>> :t fmap a2b bar
-- fmap a2b bar :: Coproduct (Pure Bool) (Pure Char) B
newtype Coproduct (f :: (i -> *) -> *) (g :: (j -> *) -> *) (a :: Either i j -> *) =
  Coproduct { getCoproduct :: (f (Compose a 'Left), g (Compose a 'Right)) }

deriving instance (Show (f (Compose a 'Left)), Show (g (Compose a 'Right))) => Show (Coproduct f g a)
deriving instance (Eq (f (Compose a 'Left)), Eq (g (Compose a 'Right))) => Eq (Coproduct f g a)
deriving instance (Ord (f (Compose a 'Left)), Ord (g (Compose a 'Right))) => Ord (Coproduct f g a)

instance (Functor f, Functor g) => Functor (Coproduct f g) where
  fmap h (Coproduct (fal, gar)) = Coproduct (Compose . h . getCompose <$> fal, Compose . h . getCompose <$> gar)

instance (Applicative f, Applicative g) => Applicative (Coproduct f g) where
  pure ax = Coproduct (pure (Compose ax), pure (Compose ax))
  Coproduct (fhl, ghr) <*> Coproduct (fal, gar) = Coproduct (liftA2 go fhl fal, liftA2 go ghr gar) where
    go (Compose hx) (Compose ax) = Compose (hx ~$~ ax)

instance (Foldable f, Foldable g) => Foldable (Coproduct f g) where
  foldMap h (Coproduct (fal, gar)) = foldMap (h . getCompose) fal <> foldMap (h . getCompose) gar

instance (Traversable f, Traversable g) => Traversable (Coproduct f g) where
  sequenceA (Coproduct (fhal, ghar)) = liftA2 teardown (setup fhal) (setup ghar) where
    setup :: (Traversable t, Applicative h) => t (Compose (Compose h a) d) -> h (Compose t (Flip (Compose2 a d)))
    setup = sequenceA . fmap (Compose . fmap Compose2 . getCompose . getCompose)

    teardown :: (Functor f, Functor g) => Compose f (Flip (Compose2 a 'Left)) y -> Compose g (Flip (Compose2 a 'Right)) y -> Compose (Coproduct f g) (Flip a) y
    teardown faly gary = Compose $ Coproduct (cleanup faly, cleanup gary)

    cleanup :: Functor t => Compose t (Flip (Compose2 a d)) y -> t (Compose (Flip a y) d)
    cleanup = fmap (Compose . Flip . getCompose2 . getFlip). getCompose

newtype Compose2 (a :: j -> k -> *) (d :: i -> j) (x :: i) (y :: k) = Compose2 { getCompose2 :: a (d x) y }

{- Pair -------------------------------------------------------------------------}

-- | A continuation kind functor for pairs.
--
-- >>> :t Pair (Identity True, Identity 'a')
-- Pair (Identity True, Identity 'a') :: Pair Bool Char Identity
newtype Pair (x0 :: k) (x1 :: k) (a :: k -> *) =
  Pair { getPair :: (a x0, a x1) }
  deriving (Show, Eq, Ord)

instance Functor (Pair x0 x1) where
  fmap f (Pair (ax0, ax1)) = Pair (f ax0, f ax1)

instance Applicative (Pair x0 x1) where
  pure ax = Pair (ax, ax)
  Pair (fx0, fx1) <*> Pair (ax0, ax1) = Pair (fx0 ~$~ ax0, fx1 ~$~ ax1) 

instance Foldable (Pair x0 x1) where
  foldMap f (Pair (ax0, ax1)) = f ax0 <> f ax1
  
instance Traversable (Pair x0 x1) where
  sequenceA (Pair (gax0, gax1)) = liftT2 (curry Pair) gax0 gax1

{- Tuple ------------------------------------------------------------------------}

-- | A continuation kind functor for tuples of arbitrary length.
--
-- >>> :t Identity True `Cons` Identity 'a' `Cons` Nil
-- Identity True `Cons` Identity 'a' `Cons` Nil
--   :: Tuple '[Bool, Char] Identity
data Tuple (xs :: [k]) (a :: k -> *) where
  Nil :: Tuple '[] a
  Cons :: a x -> !(Tuple xs a) -> Tuple (x ': xs) a
infixr 5 `Cons`

instance Show (Tuple '[] a) where
  showsPrec _ Nil = showString "Nil"
instance (Show (a x), Show (Tuple xs a)) => Show (Tuple (x ': xs) a) where
  showsPrec p (ax `Cons` t) = showParen (p > 5) $ showsPrec 6 ax . showString " `Cons` " . showsPrec 0 t

instance Eq (Tuple '[] a) where
  Nil == Nil = True
instance (Eq (a x), Eq (Tuple xs a)) => Eq (Tuple (x ': xs) a) where
  Cons ax at == Cons bx bt = ax == bx && at == bt 

instance Ord (Tuple '[] a) where
  Nil `compare` Nil = EQ
instance (Ord (a x), Ord (Tuple xs a)) => Ord (Tuple (x ': xs) a) where
  Cons ax at `compare` Cons bx bt = compare ax bx `mappend` compare at bt

instance Functor (Tuple xs) where
  fmap _ Nil = Nil
  fmap f (ax `Cons` axs) = f ax `Cons` fmap f axs

instance Applicative (Tuple '[]) where
  pure _ = Nil
  _ <*> _ = Nil

instance Applicative (Tuple xs) => Applicative (Tuple (x ': xs)) where
  pure ax = ax `Cons` pure ax
  Cons fx fxs <*> Cons ax axs = Cons (fx ~$~ ax) (fxs <*> axs)

instance Foldable (Tuple xs) where
  foldr _ z Nil = z
  foldr f z (Cons fx fxs) = f fx (foldr f z fxs)

instance Traversable (Tuple xs) where
  sequenceA Nil = pure (Compose Nil)
  sequenceA (Compose fax `Cons` cfaxs) = liftA2 go fax $ sequenceA cfaxs where
    go :: forall a x y xs. a x y -> Compose (Tuple xs) (Flip a) y -> Compose (Tuple (x ': xs)) (Flip a) y
    go axy (Compose ayxs) = Compose $ Cons (Flip axy) ayxs

{- Tagged -----------------------------------------------------------------------}

-- | A continuation kind functor for tagged unions
--
-- >>> :t [ Here (Identity True), There $ Here (Identity 'a') ]
-- [ Here (Identity True), There $ Here (Identity 'a') ]
--   :: [Tagged (Bool : Char : xs) Identity]
data Tagged (xs :: [k]) (a :: k -> *) where
  Here :: a x -> Tagged (x ': xs) a
  There :: !(Tagged xs a) -> Tagged (x ': xs) a

instance Show (Tagged '[] a) where
  showsPrec _ t = seq t $ error "Tagged '[] a is uninhabited"

instance Eq (Tagged '[] a) where
  t == t' = seq t $ seq t' $ error "Tagged '[] a is uninhabited"

instance Ord (Tagged '[] a) where
  t `compare` t' = seq t $ seq t' $ error "Tagged '[] a is uninhabited"

instance (Show (a x), Show (Tagged xs a)) => Show (Tagged (x ': xs) a) where
  showsPrec p (Here ax) = showParen (p > 10) $ showString "Here " . showsPrec 11 ax
  showsPrec p (There t) = showParen (p > 10) $ showString "There " . showsPrec 11 t

instance (Eq (a x), Eq (Tagged xs a)) => Eq (Tagged (x ': xs) a) where
  Here ax == Here bx = ax == bx
  There t == There t' = t == t'
  _ == _ = False

instance (Ord (a x), Ord (Tagged xs a)) => Ord (Tagged (x ': xs) a) where
  Here ax `compare` Here bx = ax `compare` bx
  There t `compare` There t' = t `compare` t'
  Here _ `compare` There _ = LT
  There _ `compare` Here _ = GT

instance Functor (Tagged xs) where
  fmap f (Here ax) = Here (f ax)
  fmap f (There t) = There (fmap f t)

instance Foldable (Tagged xs) where
  foldMap f (Here ax) = f ax
  foldMap f (There t) = foldMap f t

instance Traversable (Tagged xs) where
  sequenceA (Here (Compose fax)) = Compose . Here . Flip <$> fax
  sequenceA (There t) = Compose . There . getCompose <$> sequenceA t

{- Const ------------------------------------------------------------------------}

instance Functor (Const a) where
  fmap _ = Const . getConst

instance Monoid m => Applicative (Const m) where
  pure _ = Const mempty
  Const mf <*> Const ma = Const (mf <> ma)

instance Foldable (Const m) where
  foldMap _ _ = mempty

instance Traversable (Const m) where
  sequenceA (Const a) = pure $ Compose $ Const a

{- Compose ----------------------------------------------------------------------}

instance (Prelude.Functor f, Functor g) => Functor (Compose f g) where
  fmap f = Compose . Prelude.fmap (fmap f) . getCompose

instance (Prelude.Applicative f, Applicative g) => Applicative (Compose f g) where
  pure a = Compose $ Prelude.pure $ pure a
  Compose fgh <*> Compose fga = Compose $ Prelude.liftA2 (<*>) fgh fga

instance (Prelude.Foldable f, Foldable g) => Foldable (Compose f g) where
  foldMap f = Prelude.foldMap (foldMap f) . getCompose

instance (Prelude.Traversable f, Traversable g) => Traversable (Compose f g) where
  sequenceA = fmap teardown . sequenceA . setup where
    setup :: (Prelude.Functor f, Traversable g, Applicative h) => Compose f g (Compose h a) -> Dispose f (Flip a) (Compose h (Compose g))
    setup = Dispose . Prelude.fmap (Compose . sequenceA) . getCompose

    teardown :: Prelude.Functor f => Compose (Dispose f (Flip a)) (Flip (Compose g)) y -> Compose (Compose f g) (Flip a) y
    teardown = Compose . Compose . Prelude.fmap (getCompose . getFlip) . getDispose . getCompose

{- Flip -------------------------------------------------------------------------}

-- | a type-level version of 'Prelude.flip', it's used in the definition of
-- 'traverse' and 'sequenceA' as a way to reverse the order in which parameters
-- are passed.
--
-- @Flip (Flip a)@ is isomorphic to @Identity a@
--
-- >>> :t Flip . Flip
-- Flip . Flip :: a y x -> Flip (Flip a) y x
-- >>> :t getFlip . getFlip
-- getFlip . getFlip :: Flip (Flip a) x y -> a x y
newtype Flip (a :: i -> j -> *) (y :: j) (x :: i) =
  Flip { getFlip :: a x y }
  deriving (Show, Eq, Ord)
  -- XXX: Prelude.Bifunctor a => Prelude.Bifunctor (Flip a)

{- Curry ------------------------------------------------------------------------}
  
-- | a type-level version of 'Prelude.curry', it's used to convert between
-- types of kind @(i,j) -> *@ and types of kind @i -> j -> *@
newtype Curry (a :: (i,j) -> *) (x :: i) (y :: j) = Curry { getCurry :: a '(x,y) }
-- XXX: Functor (a x) => Functor (Curry (Uncurry a) x)

deriving instance Show (a '(x,y)) => Show (Curry a x y)
deriving instance Eq (a '(x,y)) => Eq (Curry a x y)
deriving instance Ord (a '(x,y)) => Ord (Curry a x y)

{- Uncurry ----------------------------------------------------------------------}

-- | A type-level version of 'Prelude.uncurry', it's used to convert between
-- types of kind @i -> j -> *@ and types of kind @(i,j) -> *@.
newtype Uncurry (a :: i -> j -> *) (z :: (i,j)) = 
  UncurryLazy { getUncurryLazy :: forall x y. (z ~ '(x,y)) => a x y }
  -- ^ The 'UncurryLazy' constructor is useful when you need to
  -- construct/destruct an @Uncurry a z@ value without placing restrictions on
  -- @z@
  --
  -- >>> :t (\(UncurryLazy axy) -> UncurryLazy axy) :: Uncurry a z -> Uncurry a z
  -- (\(UncurryLazy axy) -> UncurryLazy axy) :: Uncurry a z -> Uncurry a z
  --   :: Uncurry a z -> Uncurry a z
  -- >>> import Data.Tuple (swap)
  -- >>> :t (\(UncurryLazy axy) -> UncurryLazy $ Flip $ swap axy) :: Uncurry (,) z -> Uncurry (Flip (,)) z
  -- (\(UncurryLazy axy) -> UncurryLazy $ Flip $ swap axy) :: Uncurry (,) z -> Uncurry (Flip (,)) z
  --   :: Uncurry (,) z -> Uncurry (Flip (,)) z
  --
  -- It is slightly finnicky, and doesn't work well with function composition
  -- (i.e. @.@), and requires more hints from the compiler.
  --
  -- >>> :t (UncurryLazy . getUncurryLazy) :: Uncurry a z -> Uncurry a z
  -- <BLANKLINE>
  -- <interactive>:1:2: error:
  --     • Couldn't match type ‘a1 x0 y0’
  --                      with ‘forall x y. z1 ~ '(x, y) => a1 x y’
  -- ...
  -- >>> :t (\(UncurryLazy axy) -> UncurryLazy axy)
  -- <BLANKLINE>
  -- <interactive>:1:36: error:
  --     • Couldn't match type ‘z’ with ‘'(x, y)’
  --         arising from a use of ‘axy’
  --         because type variables ‘x’, ‘y’ would escape their scope
  -- ...


-- | The 'UncurryStrict' pattern is useful when you need to construct/destruct
-- an 'Uncurry a '(x,y)' value
--
-- >>> :t UncurryStrict . getUncurryStrict
-- UncurryStrict . getUncurryStrict
--   :: Uncurry a '(x, y) -> Uncurry a '(x, y)
-- >>> import Data.Tuple (swap)
-- >>> :t UncurryStrict . Flip . swap . getUncurryStrict
-- UncurryStrict . Flip . swap . getUncurryStrict
--   :: Uncurry (,) '(x, y) -> Uncurry (Flip (,)) '(x, y)
--
-- It works well with function composition and requires fewer hints, but cannot
-- be used to construct or match values of type @Uncurry a z@, such as are
-- needed by 'fmap'.
--
-- >>> :t (\(UncurryLazy axy) -> UncurryStrict axy) :: Uncurry a z -> Uncurry a z
-- <BLANKLINE>
-- <interactive>:1:38: error:
--     • Couldn't match type ‘z1’ with ‘'(x0, y0)’
-- ...
--     • In the first argument of ‘UncurryStrict’, namely ‘axy’
-- ...
-- >>> :t (\(UncurryStrict axy) -> UncurryLazy axy) :: Uncurry a z -> Uncurry a z
-- <BLANKLINE>
-- <interactive>:1:4: error:
--     • Couldn't match type ‘z1’ with ‘'(x0, y0)’
-- ...
--     • In the pattern: UncurryStrict axy
-- ...
--
-- However, it is very useful when paired with 'toProduct'.
pattern UncurryStrict :: a x y -> Uncurry a '(x,y)
pattern UncurryStrict axy <- (getUncurryStrict -> axy)
  where UncurryStrict axy = UncurryLazy axy

-- | a pseudo-record accessor, corresponding to matching the 'UncurryStrict'
-- pattern.  Can be useful when paired with 'fromProduct'
getUncurryStrict :: Uncurry a '(x,y) -> a x y
getUncurryStrict = getUncurryLazy

-- | a helper for lifting functions on curried types to functions
-- on their uncurried equivalents. Very useful when using the 'Functor'
-- instance for 'Product's.
--
-- >>> comma' = toProduct UncurryStrict . Pure . Compose . Pure $ ('a', True)
-- >>> :t comma'
-- comma' :: Product (Pure Char) (Pure Bool) (Uncurry (,))
-- >>> :t uncurried (const . snd) <$> comma'
-- uncurried (const . snd) <$> comma'
--   :: Product (Pure Char) (Pure Bool) (Uncurry (->))
uncurried :: (forall x y. a x y -> b x y) -> Uncurry a z -> Uncurry b z
uncurried f u = UncurryLazy $ f $ getUncurryLazy u

deriving instance Show (a x y) => Show (Uncurry a '(x,y))
deriving instance Eq (a x y) => Eq (Uncurry a '(x,y))
deriving instance Ord (a x y) => Ord (Uncurry a '(x,y))

{- Pure -------------------------------------------------------------------------}

-- | A type-level version of 'Prelude.pure' for 'Control.Monad.Cont'
-- 
-- Mainly useful when constructing continuation kind functors using
-- 'Product' and 'Coproduct'.
newtype Pure (x :: k) (a :: k -> *) = Pure { getPure :: a x }
  deriving (Show, Eq, Ord)

instance Functor (Pure x) where
  fmap h = Pure . h . getPure

instance Applicative (Pure x) where
  pure = Pure
  Pure fx <*> Pure ax = Pure (fx ~$~ ax)

instance Foldable (Pure x) where
  foldMap h (Pure ax) = h ax

instance Traversable (Pure x) where
  sequenceA (Pure ax) = liftT1 Pure ax

{--------------------------------------------------------------------------------}

-- XXX: Is ForAll useful?
--
--      newtype ForAll (a :: k -> *) = ForAll { getForAll :: forall x. a x }
--      (Functor, Applicative, Foldable, Traversable?)

-- XXX: Is Arr useful?
--
--      newtype Arr (a :: k -> *) (b :: k -> *) = Arr { runArr :: forall (x :: k). a x -> b x }
--      (Functor, Applicative)
