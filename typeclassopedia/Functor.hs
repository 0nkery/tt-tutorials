module Functor where

import           Prelude                 hiding ( Functor
                                                , fmap
                                                )

class Functor f where
    fmap :: (a -> b) -> f a -> f b

    (<$) :: a -> f b -> f a
    (<$) = fmap . const

instance Functor (Either a) where
    fmap _f (Left  x) = Left x
    fmap f  (Right x) = Right (f x)

instance Functor ((,) e) where
    fmap f (x, y) = (x, f y)

data Pair a = Pair a a

instance Functor Pair where
    fmap f (Pair x1 x2) = Pair (f x1) (f x2)

data ITree a = Leaf (Int -> a)
    | Node [ITree a]

instance Functor ITree where
    fmap f (Leaf g ) = Leaf $ f . g
    fmap f (Node ls) = Node $ map (fmap f) ls

instance Functor [] where
    fmap f []       = []
    fmap f (x : xs) = f x : f x : fmap f xs
