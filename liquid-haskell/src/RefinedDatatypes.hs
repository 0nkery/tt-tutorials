module RefinedDatatypes where

import Data.Vector

{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}
data Sparse a = SP { spDim   :: Int , spElems :: [(Int, a)] }

okSP :: Sparse String
okSP = SP 5 [(0, "cat"), (3, "dog")]

badSP :: Sparse String
badSP = SP 5 [(0, "cat"), (6, "dog")]

{-@ type SparseN a N = {v : Sparse a | spDim v == N} @-}

{-@ dotProd :: x : Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum
