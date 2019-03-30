{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Traversable where

import           Data.Tree
import           Data.Functor.Identity
import           Data.Functor.Const

listOfTreesToTreeOfLists :: [Tree a] -> Tree [a]
listOfTreesToTreeOfLists = traverse id

traverse' :: (Traversable t, Applicative f) => (a -> f b) -> t a -> f (t b)
traverse' f t = sequenceA (fmap f t)

sequenceA' :: (Traversable t, Applicative f) => t (f a) -> f (t a)
sequenceA' = traverse id

fmap' :: forall t a b . Traversable t => (a -> b) -> t a -> t b
fmap' f = runIdentity . traverse (Identity . f)

foldMap' :: (Traversable t, Monoid m) => (a -> m) -> t a -> m
foldMap' f = getConst . traverse (Const . f)

newtype L a = L [a] deriving (Functor, Foldable, Show)

instance Traversable L where
    traverse f (L []      ) = pure (L [])
    traverse f (L (l : ls)) = fmap L ((:) <$> f l <*> traverse f ls)

data MyMaybe a = Some a | None deriving (Functor, Foldable, Show)

instance Traversable MyMaybe where
    traverse f (Some m) = Some <$> f m
    traverse f None     = pure None

newtype T a b = T (a, b) deriving (Functor, Foldable, Show)

instance Traversable (T a) where
    traverse f (T (p1, p2)) = T <$> ((,) p1 <$> f p2)

data MyEither a b = Le a | Ri b deriving (Functor, Foldable, Show)

instance Traversable (MyEither a) where
    traverse f (Le e) = pure (Le e)
    traverse f (Ri e) = Ri <$> f e

newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Functor f, Functor g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (fmap (fmap f) x)

instance (Foldable f, Foldable g) => Foldable (Compose f g) where
    foldMap f (Compose t) = foldMap (foldMap f) t

instance (Traversable f, Traversable g) => Traversable (Compose f g) where
    traverse f (Compose x) = Compose <$> traverse (traverse f) x

