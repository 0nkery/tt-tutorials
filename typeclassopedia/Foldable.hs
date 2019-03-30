module Foldable where

import           Data.Monoid
import           Data.Foldable                  ( traverse_
                                                , sequenceA_
                                                )

fold' :: (Foldable t, Monoid m) => t m -> m
fold' = foldMap id

-- foldMap' :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
-- foldMap' f xs = _

foldMap' :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
foldMap' f = foldr (\x acc -> f x `mappend` acc) mempty

foldr' :: Foldable t => (a -> b -> b) -> b -> t a -> b
foldr' f z t = appEndo (foldMap (Endo . f) t) z

toList :: Foldable f => f a -> [a]
toList = foldr (:) []

foldr'' :: (a -> b -> b) -> b -> [a] -> b
foldr'' _f z []       = z
foldr'' f  z (x : xs) = foldr'' f (f x z) xs

foldr''' :: Foldable f => (a -> b -> b) -> b -> f a -> b
foldr''' f z t = foldr'' f z (toList t)

concat' :: Foldable t => t [a] -> [a]
concat' = fold'

concatMap' :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap' = foldMap

and' :: Foldable t => t Bool -> Bool
and' = getAll . foldMap All

or' :: Foldable t => t Bool -> Bool
or' = getAny . foldMap Any

all' :: Foldable t => (a -> Bool) -> t a -> Bool
all' f = getAll . foldMap (All . f)

any' :: Foldable t => (a -> Bool) -> t a -> Bool
any' f = getAny . foldMap (Any . f)

sum' :: (Foldable t, Num a) => t a -> a
sum' = getSum . foldMap Sum

sequenceA_' :: (Applicative f, Foldable t) => t (f a) -> f ()
sequenceA_' t = traverse_ (\x -> x *> pure ()) t

traverse_' :: (Applicative f, Foldable t) => (a -> f b) -> t a -> f ()
traverse_' f t = sequenceA_ (fmap f (toList t))
