module Polymorphism where

import           Prelude                 hiding ( head
                                                , abs
                                                , length
                                                )
import           Data.Vector             hiding ( head
                                                , foldl'
                                                )
import           Data.List                      ( foldl' )

{-@ type VectorN a N = {v : Vector a | vlen v == N} @-}

{-@ twoLangs :: VectorN String 2 @-}
twoLangs = fromList ["haskell", "javascript"]

{-@ type Btwn Lo Hi = {v : Int | Lo <= v && v < Hi} @-}

{-@ type NEVector a = {v : Vector a | 0 < vlen v} @-}

eeks = [ok, yup, nono]
  where
    ok   = twoLangs ! 0
    yup  = twoLangs ! 1
    nono = twoLangs ! 3

head :: Vector a -> a
head vec = vec ! 0

{-@ head' :: NEVector a -> a @-}
head' vec = vec ! 0

head'' :: Vector a -> Maybe a
head'' vec = if length vec > 0 then Just $ vec ! 0 else Nothing

{-@ unsafeLookup :: x : Int -> {v : Vector a | x < vlen v && x >= 0} -> a @-}
unsafeLookup index vec = vec ! index

{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i | ok        = Just (x ! i)
               | otherwise = Nothing
    where ok = i < length x && i >= 0

vectorSum :: Vector Int -> Int
vectorSum vec = go 0 0
  where
    go acc i | i < sz    = go (acc + (vec ! i)) (i + 1)
             | otherwise = acc
    sz = length vec

{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs n | 0 < n     = n
      | otherwise = negate n

{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum :: Vector Int -> Int
absoluteSum vec = go 0 0
  where
    go acc i | i < sz    = go (acc + abs (vec ! i)) (i + 1)
             | otherwise = acc
    sz = length vec

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go base lo
  where
    go acc i | i < hi    = go (f i acc) (i + 1)
             | otherwise = acc

vectorSum' :: Vector Int -> Int
vectorSum' vec = loop 0 n 0 body
  where
    body i acc = acc + (vec ! i)
    n = length vec

-- >>> absoluteSum' (fromList [1, -2, 3])
-- 6
{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum' vec = loop 0 n 0 body
  where
    body i acc = acc + abs (vec ! i)
    n = length vec

-- >>> dotProduct (fromList [1,2,3]) (fromList [4,5,6])
-- 32
{-@ dotProduct :: x : Vector Int -> {y : Vector Int | vlen y == vlen x} -> Int @-}
dotProduct :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 sz 0 body
  where
    body i acc = acc + (x ! i) * (y ! i)
    sz = length x

{-@ type SparseN a N = [(Btwn 0 N, a)] @-}

{-@ sparseProduct :: x : Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct x = go 0
  where
    go n []            = n
    go n ((i, v) : y') = go (n + (x ! i) * v) y'

{-@ sparseProduct' :: x : Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct' :: Vector Int -> [(Int, Int)] -> Int
sparseProduct' x = foldl' body 0 where body sum (i, v) = sum + (x ! i) * v
