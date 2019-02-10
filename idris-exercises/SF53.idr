fold_length : (l : List a) -> Nat
fold_length l = foldr (\_, n => S n) 0 l

test_fold_length1 : fold_length [4, 7, 0] = 3
test_fold_length1 = Refl

test_fold_length2 : fold_length [1] = 1
test_fold_length2 = Refl

fold_length_correct : (l : List a) -> fold_length l = length l
fold_length_correct [] = Refl
fold_length_correct (x :: xs) = rewrite fold_length_correct xs in Refl

fold_map : (f : a -> b) -> (l : List a) -> List b
fold_map f l = foldr (\el, acc => f el :: acc) [] l

fold_map_correct : (f : a -> b) -> (l : List a) -> fold_map f l = map f l
fold_map_correct f [] = Refl
fold_map_correct f (x :: xs) = rewrite fold_map_correct f xs in Refl

prod_curry : (f : (a, b) -> c) -> (x : a) -> (y : b) -> c
prod_curry f x y = f (x, y)

prod_uncurry : (f : a -> b -> c) -> (p : (a, b)) -> c
prod_uncurry f (a, b) = f a b

test_map1 : map (+3) [2, 0, 2] = [5, 3, 5]
test_map1 = Refl

uncurry_curry : (f : a -> b -> c) -> (x : a) -> (y : b) -> prod_curry (prod_uncurry f) x y = f x y
uncurry_curry f x y = Refl

curry_uncurry : (f : (a, b) -> c) -> (p : (a, b)) -> prod_uncurry (prod_curry f) p = f p
curry_uncurry f (a, b) = Refl

nth_error : (l : List x) -> (n : Nat) -> Maybe x
nth_error [] n = Nothing
nth_error (h :: l') n =
    if n == 0
        then Just h
        else nth_error l' (pred n)

out_of_bounds_nothing : (n : Nat) -> (l : List a) -> length l = n -> nth_error l n = Nothing
out_of_bounds_nothing (length []) [] Refl = Refl
out_of_bounds_nothing (length (x :: xs)) (x :: xs) Refl =
    rewrite out_of_bounds_nothing (length xs) xs Refl in
        Refl

Church : {x : Type} -> Type
Church {x} = (x -> x) -> x -> x

one : Church
one f x = f x

two : Church
two f x = f $ f x

zero : Church
zero f x = x

three : Church
three f x = f $ f $ f x

succ' : (n : Church {x}) -> Church {x}
succ' n = ?impl

succ1 : succ' zero = one
succ1 = ?succ1_rhs
