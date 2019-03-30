{-# LANGUAGE DeriveFunctor #-}
module Applicative where

import           Prelude                 hiding ( (**) )

data MyMaybe a = Some a | None deriving (Functor, Show)

instance Applicative MyMaybe where
    pure = Some

    (Some f) <*> (Some x) = Some (f x)
    _        <*> None     = None
    None     <*> _        = None

newtype ZipList a = ZipList { getZipList :: [a] }
    deriving (Functor, Show)

instance Applicative ZipList where
    pure a = ZipList $ repeat a

    (ZipList gs) <*> (ZipList xs) = ZipList (zipWith ($) gs xs)

sequenceAL :: Applicative f => [f a] -> f [a]
sequenceAL = foldl (\acc k -> (:) <$> k <*> acc) (pure [])

class Functor f => Monoidal f where
    unit :: f ()
    (**) :: f a -> f b -> f (a,b)

pure' :: Monoidal m => a -> m a
pure' x = x <$ unit

app' :: Monoidal f => f (a -> b) -> f a -> f b
app' f x = fmap (\(g, y) -> g y) (f ** x)

unit' :: Applicative f => f ()
unit' = pure ()

combine' :: Applicative f => f a -> f b -> f (a, b)
combine' f g = (,) <$> f <*> g
