nil_app : (l : List Nat) -> ([] ++ l) = l
nil_app l = Refl

tl : List Nat -> List Nat
tl [] = []
tl (x :: xs) = xs

tl_length_pred : (l : List Nat) -> pred (length l) = length (tl l)
tl_length_pred [] = Refl
tl_length_pred (x :: xs) = Refl

app_assoc : (l1, l2, l3 : List Nat) -> ((l1 ++ l2) ++ l3) = (l1 ++ (l2 ++ l3))
app_assoc [] l2 l3 = Refl
app_assoc (x :: xs) l2 l3 = rewrite app_assoc xs l2 l3 in Refl

rev : (l : List Nat) -> List Nat
rev [] = []
rev (x :: xs) = (rev xs) ++ [x]

test_rev1 : rev [1, 2, 3] = [3, 2, 1]
test_rev1 = Refl

test_rev2 : rev [] = []
test_rev2 = Refl

app_length : (l1, l2 : List Nat) -> length (l1 ++ l2) = (length l1) + (length l2)
app_length [] l2 = Refl
app_length (x :: xs) l2 = rewrite app_length xs l2 in Refl

rev_length_firsttry : (l : List Nat) -> length (rev l) = length l
rev_length_firsttry [] = Refl
rev_length_firsttry (x :: xs) =
    rewrite app_length (rev xs) [x]
        in rewrite plusCommutative (length (rev xs)) 1
            in rewrite rev_length_firsttry xs
                in Refl

app_nil_r : (l : List Nat) -> (l ++ []) = l
app_nil_r [] = Refl
app_nil_r (x :: xs) = rewrite app_nil_r xs in Refl

rev_app_distr : (l1, l2 : List Nat) -> rev (l1 ++ l2) = (rev l2) ++ (rev l1)
rev_app_distr [] l2 =
    rewrite sym (app_nil_r l2)
        in rewrite app_nil_r (rev (l2 ++ []))
            in Refl
rev_app_distr (x :: xs) l2 =
    rewrite rev_app_distr xs l2 
        in rewrite app_assoc (rev l2) (rev xs) [x]
            in Refl

rev_involutive : (l : List Nat) -> rev (rev l) = l 
rev_involutive [] = Refl
rev_involutive (x :: xs) =
    rewrite rev_app_distr (rev xs) [x]
        in rewrite rev_involutive xs
            in Refl

app_assoc4 : (l1, l2, l3, l4 : List Nat) -> (l1 ++ (l2 ++ (l3 ++ l4))) = ((l1 ++ l2) ++ l3) ++ l4
app_assoc4 [] l2 l3 l4 = rewrite app_assoc l2 l3 l4 in Refl
app_assoc4 (x :: xs) l2 l3 l4 = rewrite app_assoc4 xs l2 l3 l4 in Refl

nonzeros : List Nat -> List Nat
nonzeros [] = []
nonzeros (Z :: xs) = nonzeros xs
nonzeros (k :: xs) = k :: nonzeros xs

nonzeros_app : (l1, l2 : List Nat) -> nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
nonzeros_app [] l2 = Refl
nonzeros_app (Z :: xs) l2 = rewrite nonzeros_app xs l2 in Refl
nonzeros_app ((S k) :: xs) l2 = rewrite nonzeros_app xs l2 in Refl

beq_list_nat : (l1, l2 : List Nat) -> Bool
beq_list_nat [] [] = True
beq_list_nat (x :: xs) (y :: ys) = x == y && beq_list_nat xs ys
beq_list_nat xs ys = False

test_beq_list_nat1 : beq_list_nat [] [] = True
test_beq_list_nat1 = Refl

test_beq_list_nat2 : beq_list_nat [1, 2, 3] [1, 2, 3] = True
test_beq_list_nat2 = Refl

test_beq_list_nat3 : beq_list_nat [1, 2, 3] [1, 2, 4] = False
test_beq_list_nat3 = Refl

beq_list_nat_refl : (l : List Nat) -> True = beq_list_nat l l
beq_list_nat_refl [] = Refl
beq_list_nat_refl (Z :: xs) = rewrite beq_list_nat_refl xs in Refl
beq_list_nat_refl ((S k) :: xs) =
    rewrite beq_list_nat_refl (k :: xs) in
        Refl

total
rev_injective : (l1, l2 : List Nat) -> rev l1 = rev l2 -> l1 = l2
rev_injective [] [] prf = Refl
rev_injective xs ys prf =
    rewrite sym $ rev_involutive xs in
        rewrite sym $ rev_involutive ys in
            rewrite prf in
                Refl
