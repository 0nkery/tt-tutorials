{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MonadFix where

import           Control.Monad.Fix

newtype L a = L [a] deriving (Functor, Applicative, Monad)

instance MonadFix L where
    mfix x = mfix x >>= x
