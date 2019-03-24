module Logic where

infixr 9 ==>

{-@ (==>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False

{-@ type TRUE = {v : Bool | v} @-}
{-@ type FALSE = {v : Bool | not v} @-}

{-@ ex0 :: TRUE @-}
ex0 = True

-- {-@ ex0' :: TRUE @-}
-- ex0' = False

{-@ ex1 :: Bool -> TRUE @-}
ex1 b = b || not b

{-@ ex2 :: Bool -> FALSE @-}
ex2 b = b && not b

{-@ ex3 :: Bool -> Bool -> TRUE @-}
ex3 a b = (a && b) ==> a

{-@ ex4 :: Bool -> Bool -> TRUE @-}
ex4 a b = (a && b) ==> b

-- {-@ ex3' :: Bool -> Bool -> TRUE @-}
-- ex3' a b = (a || b) ==> a

{-@ ex5 :: Bool -> Bool -> TRUE @-}
ex5 a b = (a && (a ==> b)) ==> b

{-@ ex6 :: Bool -> Bool -> TRUE @-}
ex6 a b = a ==> (a ==> b) ==> b

{-@ exDeMorgan1 :: Bool -> Bool -> TRUE @-}
exDeMorgan1 a b = not (a || b) <=> (not a && not b)

{-@ exDeMorgan2 :: Bool -> Bool -> TRUE @-}
exDeMorgan2 a b = not (a && b) <=> (not a || not b)

{-@ ax0 :: TRUE @-}
ax0 = 1 + 1 == 2

-- {-@ ax0' :: TRUE @-}
-- ax0' = 1 + 1 == 3

{-@ ax1 :: Int -> TRUE @-}
ax1 :: Int -> Bool
ax1 x = x < x + 1

-- {-@ ax2 :: (Ord a, Num a) => a -> TRUE @-}
ax2 x = (x < 0) ==> (0 <= negate x)

{-@ ax3 :: (Ord a, Num a) => a -> a -> TRUE @-}
ax3 x y = (0 <= x) ==> (0 <= y) ==> (0 <= x + y)

{-@ ax4 :: (Eq a, Num a) => a -> a -> TRUE @-}
ax4 x y = (x == y - 1) ==> (x + 2 == y + 1)

{-@ ax5 :: (Ord a, Num a) => a -> a -> a -> TRUE @-}
ax5 x y z = (x <= 0 && x >= 0) ==> (y == x + z) ==> (y == z)

{-@ ax6 :: (Ord a, Num a) => a -> a -> TRUE @-}
ax6 x y = (y >= 0) ==> (x <= x + y)

-- {- measure f :: Int -> Int @-}

-- -- {-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
-- -- congruence :: (Int -> Int) -> Int -> Int -> Bool
-- -- congruence f x y = (x == y) ==> (f x == f y)

-- {-@ fx1 :: (Int -> Int) -> Int -> TRUE @-}
-- fx1 :: (Int -> Int) -> Int -> Bool
-- fx1 f x =   (x == f (f (f x)))
--         ==> (x == f (f (f (f (f x)))))
--         ==> (x == f x)

{-@ measure size @-}
size :: [a] -> Int
size []        = 0
size (_x : xs) = 1 + size xs

{-@ fx0 :: Eq a => [a] -> [a] -> TRUE @-}
fx0 xs ys = (xs == ys) ==> (size xs == size ys)

-- {-@ fx2 :: a -> [a] -> TRUE @-}
-- fx2 x xs = 0 <= size ys
--     where
--         ys = x : xs

{-@ fxVC2 :: p -> [a1] -> [a2] -> TRUE @-}
fxVC2 x xs ys = (0 <= size xs) ==> (size ys == 1 + size xs) ==> (0 < size ys)
