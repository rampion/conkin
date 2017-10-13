{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Conkin 
  ( Cont
  {- classes -}
  , Functor(..), (<$>)
  , Applicative(..), type (~>)(..), liftA2, liftA3
  , Foldable(..)
  , Traversable(..)
  {- wrappers -}
  , Conkin(..)
  , Coyoneda(..), getCoyoneda, toCoyoneda
  {- functors -}
  , Product(..)
  , Coproduct(..)
  , Pair(..)
  , Tuple(..)
  , Tagged(..)
  {- utility types -}
  , Flip(..)
  --, Exists(..)
  --, Both(..)
  --, Curry(..)
  --, Curry2(..)
  --, Compose2(..)
  ) where
import Prelude hiding (Functor(..), (<$>), Applicative(..), Traversable(..), Foldable(..) )
import qualified Prelude
import qualified Control.Applicative as Prelude
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Kind
import Data.Monoid (Endo(..), (<>))
import Unsafe.Coerce (unsafeCoerce)

type Cont r a = (a -> r) -> r

{- Classes ----------------------------------------------------------------------}

{-| A Functor from Hask^k to Hask #-}
class Functor (f :: Cont Type k) where
  fmap :: (forall (x :: k). a x -> b x) -> f a -> f b

infixl 4 <$>
(<$>) :: Functor f => (forall x. a x -> b x) -> f a -> f b 
(<$>) = fmap

infixl 4 <*>
class Functor f => Applicative (f :: Cont Type k) where
  pure :: (forall (x :: k). a x) -> f a
  (<*>) :: f (a ~> b) -> f a -> f b

{-| a ~> b is an arrow in Hask^k #-}
newtype (~>) (a :: k -> *) (b :: k -> *) (x :: k) =
  Arrow { (~$~) :: a x -> b x }

liftA2 :: Applicative f => (forall x. a x -> b x -> c x) -> f a -> f b -> f c
liftA2 f a b = (Arrow . f) <$> a <*> b

liftA3 :: Applicative f => (forall x. a x -> b x -> c x -> d x) -> f a -> f b -> f c -> f d
liftA3 f a b c = Arrow . (Arrow .) . f <$> a <*> b <*> c

class Foldable (t :: Cont Type k) where
  foldr :: (forall (x :: k). a x -> b -> b ) -> b -> t a -> b
  foldr f b ta = foldMap (Endo . f) ta `appEndo` b

  foldMap :: Monoid m => (forall (x :: k). a x -> m) -> t a -> m
  foldMap f = foldr (\ax b -> f ax <> b) mempty

  {-# MINIMAL foldr | foldMap #-}

class (Foldable t, Functor t) => Traversable (t :: Cont Type k) where
  traverse :: Applicative f => (forall x. a x -> f (b x)) -> t a -> f (Compose t (Flip b))
  traverse f = sequenceA . fmap (Compose . f)

  sequenceA :: Applicative f => t (Compose f a) -> f (Compose t (Flip a))
  sequenceA = traverse getCompose

  {-# MINIMAL traverse | sequenceA #-}

newtype Flip (a :: i -> j -> *) (y :: j) (x :: i) =
  Flip { getFlip :: a x y }

{- Conkin -----------------------------------------------------------------------}

-- If `f` is a functor from Hask to Hask, then forall x :: k, `Conkin f x` is a
-- functor from Hask^k to Hask
newtype Conkin (f :: * -> *) (x :: k) (a :: k -> *) =
  -- Conkin f ~ Flip (Compose f)
  Conkin { getConkin :: f (a x) }

instance Prelude.Functor f => Functor (Conkin f x) where
  fmap f (Conkin fx) = Conkin $ Prelude.fmap f fx
  
instance Prelude.Applicative f => Applicative (Conkin f x) where
  pure a = Conkin $ Prelude.pure a
  Conkin ff <*> Conkin fa = Conkin $ Prelude.liftA2 (~$~) ff fa

instance Prelude.Foldable t => Foldable (Conkin t x) where
  foldr f b = Prelude.foldr f b . getConkin
  foldMap f = Prelude.foldMap f . getConkin

instance Prelude.Traversable t => Traversable (Conkin t x) where
  sequenceA = teardown . Prelude.traverse setup . getConkin where
    setup :: Compose f a x -> Coyoneda f (Exists (a x))
    setup = Coyoneda Exists . getCompose

    teardown :: (Functor f, Prelude.Functor t) => Coyoneda f (t (Exists (a x))) -> f (Compose (Conkin t x) (Flip a))
    teardown (Coyoneda k fax) = Compose . Conkin . Prelude.fmap Flip . unwrap k <$> fax

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

{-
instance Traversable (Conkin [] x) where
  sequenceA = Prelude.foldr cons nil . getConkin where
    nil :: Applicative f => f (Compose (Conkin [] x) (Flip a))
    nil = pure $ Compose $ Conkin []

    cons :: Applicative f => Compose f a x -> f (Compose (Conkin [] x) (Flip a)) -> f (Compose (Conkin [] x) (Flip a))
    cons = liftA2 (\axy (Compose (Conkin ayxs)) -> Compose $ Conkin $ Flip axy : ayxs) . getCompose

instance Traversable (Conkin Maybe x) where
  sequenceA = maybe nothing just . getConkin where
    nothing :: Applicative f => f (Compose (Conkin Maybe x) (Flip a))
    nothing = pure $ Compose $ Conkin Nothing

    just :: Applicative f => Compose f a x -> f (Compose (Conkin Maybe x) (Flip a))
    just = fmap (Compose . Conkin . Just . Flip) . getCompose

instance Traversable (Conkin (Either a) x) where
  sequenceA = either left right . getConkin where
    left :: Applicative f => a -> f (Compose (Conkin (Either a) x) (Flip b))
    left a = pure $ Compose $ Conkin $ Left a

    right :: Applicative f => Compose f b x -> f (Compose (Conkin (Either a) x) (Flip b))
    right = fmap (Compose . Conkin . Right . Flip) . getCompose

instance Traversable (Conkin (Const m) x) where
  sequenceA (Conkin (Const m)) = pure $ Compose $ Conkin $ Const m

instance Traversable (Conkin ((,) a) x) where
  sequenceA (Conkin (a, Compose faxy)) = fmap (\axy -> Compose $ Conkin (a, Flip axy)) faxy
-}


{- Coyoneda ---------------------------------------------------------------------}

-- If `t` is a functor from Hask^k to Hask, then 
-- `Coyoneda t` is a functor from Hask to Hask.
data Coyoneda (t :: (k -> *) -> *) (a :: *) where
  Coyoneda :: (forall x. a x -> b) -> t a -> Coyoneda t b

getCoyoneda :: Functor t => Coyoneda t a -> t (Const a)
getCoyoneda (Coyoneda f t) = Const . f <$> t

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

instance Foldable t => Prelude.Foldable (Coyoneda t) where
  foldr f b (Coyoneda k t) = foldr (f . k) b t
  foldMap f (Coyoneda k t) = foldMap (f . k) t

instance Traversable t => Prelude.Traversable (Coyoneda t) where
  sequenceA (Coyoneda k t) = Prelude.fmap teardown . getConkin . sequenceA $ setup . k <$> t where
    setup :: Prelude.Functor f => f a -> Compose (Conkin f y) (Curry (Const a)) x
    setup = Compose . Conkin . Prelude.fmap (Curry . Const)

    teardown :: Functor t => Compose t (Flip (Curry (Const a))) y -> Coyoneda t a
    teardown = Coyoneda (getConst . getCurry . getFlip) . getCompose
  
newtype Curry (a :: (i,j) -> *) (x :: i) (y :: j) = Curry { getCurry :: a '(x,y) }

{- Product ----------------------------------------------------------------------}

newtype Product (f :: (i -> *) -> *) (g :: (j -> *) -> *) (a :: (i,j) -> *) =
  Product { getProduct :: f (Compose g (Curry a)) }

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

newtype Coproduct (f :: (i -> *) -> *) (g :: (j -> *) -> *) (a :: Either i j -> *) =
  Coproduct { getCoproduct :: (f (Compose a 'Left), g (Compose a 'Right)) }

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

newtype Pair (x0 :: k) (x1 :: k) (a :: k -> *) =
  Pair { getPair :: (a x0, a x1) }

instance Functor (Pair x0 x1) where
  fmap f (Pair (ax0, ax1)) = Pair (f ax0, f ax1)

instance Applicative (Pair x0 x1) where
  pure ax = Pair (ax, ax)
  Pair (fx0, fx1) <*> Pair (ax0, ax1) = Pair (fx0 ~$~ ax0, fx1 ~$~ ax1) 

instance Foldable (Pair x0 x1) where
  foldMap f (Pair (ax0, ax1)) = f ax0 <> f ax1
  
instance Traversable (Pair x0 x1) where
  traverse f (Pair (ax0, ax1)) = liftA2 (\bx0 bx1 -> Compose $ Pair (Flip bx0, Flip bx1)) (f ax0) (f ax1)

{- Tuple ------------------------------------------------------------------------}

data Tuple (xs :: [k]) (a :: k -> *) where
  Nil :: Tuple '[] a
  Cons :: a x -> !(Tuple xs a) -> Tuple (x ': xs) a
infixr 5 `Cons`

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

data Tagged (xs :: [k]) (a :: k -> *) where
  Here :: a x -> Tagged (x ': xs) a
  There :: !(Tagged xs a) -> Tagged (x ': xs) a

instance Functor (Tagged xs) where
  fmap f (Here ax) = Here (f ax)
  fmap f (There t) = There (fmap f t)

instance Foldable (Tagged xs) where
  foldMap f (Here ax) = f ax
  foldMap f (There t) = foldMap f t

instance Traversable (Tagged xs) where
  sequenceA (Here (Compose fax)) = Compose . Here . Flip <$> fax
  sequenceA (There t) = Compose . There . getCompose <$> sequenceA t
