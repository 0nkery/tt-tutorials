nth_error : (l : List Nat) -> (n : Nat) -> Maybe Nat
nth_error [] n = Nothing
nth_error (x :: xs) n =
    case n == 0 of
        True => Just x
        False => nth_error xs (pred n)

test_nth_error1 : nth_error [4, 5, 6, 7] 0 = Just 4
test_nth_error1 = Refl

test_nth_error2 : nth_error [4, 5, 6, 7] 3 = Just 7
test_nth_error2 = Refl

test_nth_error3 : nth_error [4, 5, 6, 7] 9 = Nothing
test_nth_error3 = Refl

option_elim : (default : Nat) -> (o : Maybe Nat) -> Nat
option_elim default Nothing = default
option_elim default (Just x) = x

hd_error : (l : List Nat) -> Maybe Nat
hd_error [] = Nothing
hd_error (x :: xs) = Just x

test_hd_error1 : hd_error [] = Nothing
test_hd_error1 = Refl

test_hd_error2 : hd_error [1] = Just 1
test_hd_error2 = Refl

test_hd_error3 : hd_error [5, 6] = Just 5
test_hd_error3 = Refl

hd : (default : Nat) -> (l : List Nat) -> Nat
hd default [] = default
hd default (x :: xs) = x

option_elim_hd : (l : List Nat) -> (default : Nat) -> hd default l = option_elim default (hd_error l)
option_elim_hd [] default = Refl
option_elim_hd (x :: xs) default = Refl