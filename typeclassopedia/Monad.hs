{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Monad where

import qualified Control.Monad                 as M

newtype List a = List [a] deriving (Functor, Applicative, Show)

instance Monad List where
  xs >>= f = (fmap f xs) >>= id

newtype R e a = R (e -> a) deriving (Functor, Applicative)

instance Monad (R e) where
  (R r) >>= f = R (\env -> f (r env)) >>= id

data Free f a = Var a | Node (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap g (Var  x) = Var (g x)
  fmap g (Node x) = Node $ fmap (fmap g) x

instance Functor f => Applicative (Free f) where
  pure x = Var x

  (Var  f) <*> x = fmap f x
  (Node f) <*> x = Node $ fmap (<*> x) f

instance Functor f => Monad (Free f) where
  (Var  x) >>= f = f x
  (Node x) >>= f = Node $ fmap ((>>= id) . fmap f) x

class Applicative m => Monad'' m where
  join :: m (m a) -> m a

bind' :: Monad'' m => m a -> (a -> m b) -> m b
bind' x f = join (fmap f x)

join' :: Monad m => m (m a) -> m a
join' x = x >>= id

fmap' :: Monad m => (a -> b) -> m a -> m b
fmap' f x = x >>= (return . f)

join''
  :: forall m n a
   . (Traversable m, Traversable n, Monad m, Monad n)
  => m (n (m (n a)))
  -> m (n a)
join'' = squash
 where
  cut :: (Traversable t, Monad t, Monad m) => t (m (t a)) -> m (t a)
  cut = fmap M.join . sequence

  squash :: (Traversable t, Monad t, Monad m) => m (t (m (t a))) -> m (t a)
  squash = (>>= cut)
