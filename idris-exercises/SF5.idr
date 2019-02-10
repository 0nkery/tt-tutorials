module Poly

%access public export

%default total

repeat : (x : x_ty) -> (count : Nat) -> List x_ty
repeat x Z = []
repeat x (S k) = x :: repeat x k

test_repeat1 : repeat 4 2 = [4, 4]
test_repeat1 = Refl

test_repeat2 : repeat False 1 = [False]
test_repeat2 = Refl

namespace MumbleGrumble
    data Mumble : Type where
        A : Mumble
        B : Mumble -> Nat -> Mumble
        C : Mumble

    data Grumble : (x : Type) -> Type where
        D : Mumble -> Grumble x
        E : x -> Grumble x

rev : (l : List a) -> List a
rev [] = []
rev (h :: t) = (rev t) ++ [h]

test_rev1 : rev [1, 2] = [2, 1]
test_rev1 = Refl

test_rev2 : rev [True] = [True]
test_rev2 = Refl

len : (l : List a) -> Nat
len [] = Z
len (h :: t) = S (len t)

test_length1 : length [1, 2, 3] = 3
test_length1 = Refl

app_nil_r : (l : List a) -> l ++ [] = l
app_nil_r [] = Refl
app_nil_r (x :: xs) = rewrite app_nil_r xs in Refl

app_nil : (l : List a) -> [] ++ l = l
app_nil l = Refl

app_assoc : (l, m, n : List a) -> l ++ m ++ n = (l ++ m) ++ n
app_assoc [] m n = Refl
app_assoc (x :: xs) m n = rewrite app_assoc xs m n in Refl

app_length : (l1, l2 : List a) -> length (l1 ++ l2) = length l1 + length l2
app_length [] l2 = Refl
app_length (x :: xs) l2 = rewrite app_length xs l2 in Refl

rev_app_distr : (l1, l2 : List a) -> rev (l1 ++ l2) = rev l2 ++ rev l1
rev_app_distr [] l2 = rewrite app_nil_r (rev l2) in Refl
rev_app_distr (x :: xs) l2 =
    rewrite rev_app_distr xs l2 in
        rewrite sym $ app_assoc (rev l2) (rev xs) [x] in
            Refl

rev_involutive : (l : List a) -> rev (rev l) = l
rev_involutive [] = Refl
rev_involutive (x :: xs) =
    rewrite rev_app_distr (rev xs) [x] in
        rewrite rev_involutive xs in
            Refl

split : (l : List (x, y)) -> (List x, List y)
split [] = ([], [])
split ((a, b) :: xs) =
    let
        (ys, zs) = split xs
    in
        (a :: ys, b :: zs)

test_split : split [(1, False), (2, False)] = ([1, 2], [False, False])
test_split = Refl

nth_error : (l : List a) -> (n : Nat) -> Maybe a
nth_error [] n = Nothing
nth_error (x :: xs) Z = Just x
nth_error (x :: xs) (S k) = nth_error xs k

test_nth_error1 : nth_error [4, 5, 6, 7] 0 = Just 4
test_nth_error1 = Refl

test_nth_error2 : nth_error [[1], [2]] 1 = Just [2]
test_nth_error2 = Refl

test_nth_error3 : nth_error [True] 2 = Nothing
test_nth_error3 = Refl

hd_error : (l : List a) -> Maybe a
hd_error [] = Nothing
hd_error (x :: xs) = Just x

test_hd_error1 : hd_error [1, 2] = Just 1
test_hd_error1 = Refl

test_hd_error2 : hd_error [[1], [2]] = Just [1]
test_hd_error2 = Refl

map_rev : (f : x -> y) -> (l : List x) -> map f (rev l) = rev (map f l)
map_rev f [] = Refl
map_rev f (x :: xs) = ?map_rev_rhs_2
