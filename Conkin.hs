{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeInType #-}
module Conkin where
import Data.Kind

type Cont r a = (a -> r) -> r

class FunctorK (f :: Cont Type k) where
  fmapk :: (forall (x :: k). a x -> b x) -> f a -> f b

newtype Pair (x0 :: k) (x1 :: k) (a :: k -> *) =
  Pair { getPair :: (a x0, a x1) }

instance FunctorK (Pair x0 x1) where
  fmapk f (Pair (ax0, ax1)) = Pair (f ax0, f ax1)
