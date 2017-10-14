{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- just used for deriving
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Conkin 
  ( align
  , apportion
  ( Cont
  {- classes -}
  , Functor(..), (<$>)
  , Applicative(..), type (~>)(..), liftA2, liftA3
  , Foldable(..)
  , Traversable(..)
  {- wrappers -}
  , Dispose(..)
  , Coyoneda(..), getCoyoneda, toCoyoneda
  {- functors -}
  , Product(..)
  , Coproduct(..)
  , Pair(..)
  , Tuple(..)
  , Tagged(..)
  {- utility types -}
  , Flip(..)
  , Curry(..)
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
import Data.Kind (type (*), Type)
import Data.Monoid (Endo(..), (<>))
import Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Identity (Identity(..))

align :: (Prelude.Traversable f, Applicative g) => f (g Identity) -> g f
align = fmap teardown . sequenceA . Dispose . Prelude.fmap setup where
  setup :: Functor g => g Identity -> Compose g (Flip Const) void
  setup = Compose . fmap (Flip . Const . runIdentity)

  teardown :: Prelude.Functor f => Compose (Dispose f void) (Flip (Flip Const)) x -> f x
  teardown = Prelude.fmap (getConst . getFlip . getFlip) . getDispose . getCompose

apportion :: (Prelude.Applicative f, Traversable g) => g f -> f (g Identity)
apportion = Prelude.fmap teardown . getDispose . traverse setup where
  setup :: Prelude.Functor f => f x -> Dispose f void (Const x)
  setup = Dispose . Prelude.fmap Const

  teardown :: Functor g => Compose g (Flip Const) void -> g Identity
  teardown = fmap (Identity . getConst . getFlip) . getCompose

type Cont r a = (a -> r) -> r

{- Classes ----------------------------------------------------------------------}

{-| A functor from Hask^k to Hask -}
class Functor (f :: Cont Type k) where
  fmap :: (forall (x :: k). a x -> b x) -> f a -> f b

(<$>) :: Functor f => (forall x. a x -> b x) -> f a -> f b 
(<$>) = fmap
infixl 4 <$>

class Functor f => Applicative (f :: Cont Type k) where
  pure :: (forall (x :: k). a x) -> f a
  (<*>) :: f (a ~> b) -> f a -> f b
infixl 4 <*>

{-| arrows in Hask^k have type `forall x. (a ~> b) x -}
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
  deriving (Show, Eq, Ord)

{- Dispose -----------------------------------------------------------------------}

-- If `f` is a functor from Hask to Hask, then forall x :: k, `Dispose f x` is a
-- functor from Hask^k to Hask
newtype Dispose (f :: * -> *) (x :: k) (a :: k -> *) =
  -- Dispose f ~ Flip (Compose f)
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

{-
instance Traversable (Dispose [] x) where
  sequenceA = Prelude.foldr cons nil . getDispose where
    nil :: Applicative f => f (Compose (Dispose [] x) (Flip a))
    nil = pure $ Compose $ Dispose []

    cons :: Applicative f => Compose f a x -> f (Compose (Dispose [] x) (Flip a)) -> f (Compose (Dispose [] x) (Flip a))
    cons = liftA2 (\axy (Compose (Dispose ayxs)) -> Compose $ Dispose $ Flip axy : ayxs) . getCompose

instance Traversable (Dispose Maybe x) where
  sequenceA = maybe nothing just . getDispose where
    nothing :: Applicative f => f (Compose (Dispose Maybe x) (Flip a))
    nothing = pure $ Compose $ Dispose Nothing

    just :: Applicative f => Compose f a x -> f (Compose (Dispose Maybe x) (Flip a))
    just = fmap (Compose . Dispose . Just . Flip) . getCompose

instance Traversable (Dispose (Either a) x) where
  sequenceA = either left right . getDispose where
    left :: Applicative f => a -> f (Compose (Dispose (Either a) x) (Flip b))
    left a = pure $ Compose $ Dispose $ Left a

    right :: Applicative f => Compose f b x -> f (Compose (Dispose (Either a) x) (Flip b))
    right = fmap (Compose . Dispose . Right . Flip) . getCompose

instance Traversable (Dispose (Const m) x) where
  sequenceA (Dispose (Const m)) = pure $ Compose $ Dispose $ Const m

instance Traversable (Dispose ((,) a) x) where
  sequenceA (Dispose (a, Compose faxy)) = fmap (\axy -> Compose $ Dispose (a, Flip axy)) faxy
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
  sequenceA (Coyoneda k t) = Prelude.fmap teardown . getDispose . sequenceA $ setup . k <$> t where
    setup :: Prelude.Functor f => f a -> Compose (Dispose f y) (Curry (Const a)) x
    setup = Compose . Dispose . Prelude.fmap (Curry . Const)

    teardown :: Functor t => Compose t (Flip (Curry (Const a))) y -> Coyoneda t a
    teardown = Coyoneda (getConst . getCurry . getFlip) . getCompose
  
newtype Curry (a :: (i,j) -> *) (x :: i) (y :: j) = Curry { getCurry :: a '(x,y) }

deriving instance Show (a '(x,y)) => Show (Curry a x y)
deriving instance Eq (a '(x,y)) => Eq (Curry a x y)
deriving instance Ord (a '(x,y)) => Ord (Curry a x y)

{- Product ----------------------------------------------------------------------}

newtype Product (f :: (i -> *) -> *) (g :: (j -> *) -> *) (a :: (i,j) -> *) =
  Product { getProduct :: f (Compose g (Curry a)) }

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
  traverse f (Pair (ax0, ax1)) = liftA2 (\bx0 bx1 -> Compose $ Pair (Flip bx0, Flip bx1)) (f ax0) (f ax1)

{- Tuple ------------------------------------------------------------------------}

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
