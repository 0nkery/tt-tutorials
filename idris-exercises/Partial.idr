infix 5 ^

(^) : Nat -> %static Nat -> Nat
(^) x Z = 1
(^) x (S k) = mult x (x ^ k)

powFn : Nat -> Nat
powFn x = (x ^ 2) + 1

calc : Int -> Int
calc x = (x * x) + x

myMap : %static (a -> b) -> List a -> List b
myMap f [] = []
myMap f (x :: xs) = f x :: myMap f xs

doubleAll : List Int -> List Int
doubleAll xs = myMap (* 2) xs
