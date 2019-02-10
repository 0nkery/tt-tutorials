module Lists

%default total

data NatProd : Type where
    Pair : Nat -> Nat -> NatProd

syntax "(" [x] "," [y] ")" = Pair x y

fst : (p : NatProd) -> Nat
fst (Pair x y) = x

snd : (p : NatProd) -> Nat
snd (Pair x y) = y

swap : (p : NatProd) -> NatProd
swap (x, y) = (y, x)

surjective_pairing : (n, m : Nat) -> (n, m) = (fst (n, m), snd(n, m))
surjective_pairing n m = Refl

surjective_pairing_stuck : (p : NatProd) -> p = (fst p, snd p)
surjective_pairing_stuck (Pair k j) = Refl

snd_fst_is_swap : (p : NatProd) -> (snd p, fst p) = swap p
snd_fst_is_swap (Pair k j) = Refl

fst_swap_is_snd : (p : NatProd) -> fst (swap p) = snd p
fst_swap_is_snd (Pair k j) = Refl

data NatList : Type where
    Nil : NatList
    Cons : Nat -> NatList -> NatList

(::) : Nat -> NatList -> NatList
(::) n l = Cons n l

mylist : NatList
mylist = [1, 2, 3]

repeat : (n, count : Nat) -> NatList
repeat n Z = Nil
repeat n (S k) = n :: repeat n k

length : (l : NatList) -> Nat
length [] = Z
length (Cons k x) = S (length x)

append : (l1, l2 : NatList) -> NatList
append Nil l2 = l2
append (Cons h t) l2 = h :: append t l2

(++) : NatList -> NatList -> NatList
(++) = append

test_append1 : ([1, 2, 3] ++ [4, 5]) = [1, 2, 3, 4, 5]
test_append1 = Refl

test_append2 : (Nil ++ [4, 5]) = [4, 5]
test_append2 = Refl

test_append3 : [1, 2, 3] ++ [] = [1, 2, 3]
test_append3 = Refl

hd : (default : Nat) -> (l : NatList) -> Nat
hd default Nil = default
hd default (Cons h t) = h

tl : (l : NatList) -> NatList
tl Nil = Nil
tl (Cons h t) = t

test_hd1 : hd 0 [1, 2, 3] = 1
test_hd1 = Refl

test_hd2 : hd 0 [] = 0
test_hd2 = Refl

test_tl : tl [1, 2, 3] = [2, 3]
test_tl = Refl

non_zeros : (l : NatList) -> NatList
non_zeros [] = Nil
non_zeros (Cons Z x) = non_zeros x
non_zeros (Cons k x) = k :: non_zeros x

test_nonzeros : non_zeros [0, 1, 0, 2, 3, 0, 0] = [1, 2, 3]
test_nonzeros = Refl

oddmembers : (l : NatList) -> NatList
oddmembers [] = Nil
oddmembers (Cons k x) =
    if modNatNZ k 2 SIsNotZ == 0
        then oddmembers x
        else k :: oddmembers x

test_oddmembers : oddmembers [0, 1, 0, 2, 3, 0, 0] = [1, 3]
test_oddmembers = Refl

count_oddmembers : (l : NatList) -> Nat
count_oddmembers = length . oddmembers

test_count_oddmembers : count_oddmembers [1, 0, 3, 1, 4, 5] = 4
test_count_oddmembers = Refl

alternate : (l1, l2 : NatList) -> NatList
alternate [] l2 = l2
alternate l1 [] = l1
alternate (Cons k x) (Cons j y) = k :: j :: alternate x y

test_alternate1 : alternate [1, 2, 3] [4, 5, 6] = [1, 4, 2, 5, 3, 6]
test_alternate1 = Refl
test_alternate2 : alternate [1] [4, 5, 6] = [1, 4, 5, 6]
test_alternate2 = Refl
test_alternate3 : alternate [1, 2, 3] [4] = [1, 4, 2, 3]
test_alternate3 = Refl
test_alternate4 : alternate [] [20, 30] = [20, 30]
test_alternate4 = Refl

Bag : Type
Bag = NatList

count : (v : Nat) -> (s : Bag) -> Nat
count v [] = Z
count Z (Cons Z x) = S (count Z x)
count v@(S k) (Cons (S j) x) = count k [j] + count v x
count v (Cons k x) = count v x

test_count : count 1 [1, 2, 3, 1, 4, 1] = 3
test_count = Refl
test_count2 : count 6 [1, 2, 3, 1, 4, 1] = 0
test_count2 = Refl

sum : Bag -> Bag -> Bag
sum = append

test_sum1 : count 1 (sum [1, 2, 3] [1, 4, 1]) = 3
test_sum1 = Refl

add : (v : Nat) -> (s : Bag) -> Bag
add = (::)

test_add1 : count 1 (add 1 [1, 4, 1]) = 3
test_add1 = Refl
test_add2 : count 5 (add 1 [1, 4, 1]) = 0
test_add2 = Refl

member : (v : Nat) -> (s : Bag) -> Bool
member v [] = False
member v (Cons k x) =
    if k == v
        then True
        else member v x

test_member1 : member 1 [1, 4, 1] = True
test_member1 = Refl
test_member2 : member 2 [1, 4, 1] = False
test_member2 = Refl

remove_one : (v : Nat) -> (s : Bag) -> Bag
remove_one v [] = []
remove_one v (Cons k x) =
    if k == v
        then x
        else k :: remove_one v x

test_remove_one1 : count 5 (remove_one 5 [2, 1, 5, 4, 1]) = 0
test_remove_one1 = Refl
test_remove_one2 : count 5 (remove_one 5 [2, 1, 4, 1]) = 0
test_remove_one2 = Refl
test_remove_one3 : count 4 (remove_one 5 [2, 1, 5, 4, 1, 4]) = 2
test_remove_one3 = Refl
test_remove_one4 : count 5 (remove_one 5 [2, 1, 5, 4, 5, 1, 4]) = 1
test_remove_one4 = Refl

remove_all : (v : Nat) -> (s : Bag) -> Bag
remove_all v [] = []
remove_all v (Cons k x) =
    if k == v
        then remove_all v x
        else k :: remove_all v x

test_remove_all1 : count 5 (remove_all 5 [2, 1, 5, 4, 1]) = 0
test_remove_all1 = Refl
test_remove_all2 : count 5 (remove_all 5 [2, 1, 4, 1]) = 0
test_remove_all2 = Refl
test_remove_all3 : count 4 (remove_all 5 [2, 1, 5, 4, 1, 4]) = 2
test_remove_all3 = Refl
test_remove_all4 : count 5 (remove_all 5 [2, 1, 5, 4, 5, 1, 4, 5, 1, 4]) = 0
test_remove_all4 = Refl

subset : (s1 : Bag) -> (s2 : Bag) -> Bool
subset [] s2 = True
subset (Cons k x) s2 =
    let
        contains_elem_of_s1 = member k s2
        s2' = remove_one k s2
    in
        contains_elem_of_s1 && subset x s2'

test_subset1 : subset [1, 2] [2, 1, 4, 1] = True
test_subset1 = Refl

test_subset2 : subset [1, 2, 2] [2, 1, 4, 1] = False
test_subset2 = Refl

add_succ_count : (v : Nat) -> (s : Bag) -> count v (add v s) = S (count v s)
add_succ_count Z s = Refl
add_succ_count (S k) [] = rewrite add_succ_count k [] in Refl
add_succ_count (S k) (Cons j x) = rewrite add_succ_count k [] in Refl

ble_n_Sn : (n : Nat) -> n `lte` (S n) = True
ble_n_Sn Z = Refl
ble_n_Sn (S k) = rewrite ble_n_Sn k in Refl

count_member_nonzero : (s : Bag) -> 1 `lte` count 1 (1 :: s) = True
count_member_nonzero s = Refl

remove_decreases_count : (s : Bag) -> lte (count 0 (remove_one 0 s)) (count 0 s) = True
remove_decreases_count [] = Refl
remove_decreases_count (Cons Z x) = rewrite ble_n_Sn (count 0 x) in Refl
remove_decreases_count (Cons (S k) x) = rewrite remove_decreases_count x in Refl

bag_count_sum : (s1, s2 : Bag) -> count 0 (sum s1 s2) = (count 0 s1) + (count 0 s2)
bag_count_sum [] s2 = Refl
bag_count_sum (Cons Z x) s2 = rewrite bag_count_sum x s2 in Refl
bag_count_sum (Cons (S k) x) s2 = rewrite bag_count_sum x s2 in Refl
