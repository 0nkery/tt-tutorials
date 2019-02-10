mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z = Refl
mult_0_r (S k) =
    let indHypothesis = mult_0_r k in
        rewrite indHypothesis in Refl

plus_0_r : (n : Nat) -> n + 0 = n
plus_0_r Z = Refl
plus_0_r (S k) = rewrite plus_0_r k in Refl

plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
plus_n_Sm Z m = Refl
plus_n_Sm (S k) j = rewrite plus_n_Sm k j in Refl

total
plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm Z Z = Refl
plus_comm Z (S k) = rewrite plus_comm Z k in Refl
plus_comm (S k) m = rewrite plus_comm k m in rewrite plus_n_Sm m k in Refl

total
plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
plus_assoc Z m p = Refl
plus_assoc (S k) m n = rewrite plus_assoc k m n in Refl

double : (n : Nat) -> Nat
double Z = Z
double (S k) = S (S (double k))

total
double_plus : (n : Nat) -> double n = n + n
double_plus Z = Refl
double_plus (S k) = rewrite double_plus k in rewrite plus_n_Sm k k in Refl

evenb : (n : Nat) -> Bool
evenb Z = True
evenb (S Z) = False
evenb (S (S k)) = evenb k

total
not_involutive : (b : Bool) -> not (not b) = b
not_involutive True = Refl
not_involutive False = Refl

total
evenb_S : (n : Nat) -> evenb (S n) = not (evenb n)
evenb_S Z = Refl
evenb_S (S k) = rewrite evenb_S k in rewrite not_involutive (evenb k) in Refl

total
plus_rearrange : (n, m, p, q : Nat) -> (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange n m p q = rewrite plus_comm n m in Refl

total
plus_swap : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap n m p =
    rewrite plus_assoc n m p in
        rewrite plus_comm n m in
            rewrite plus_assoc m n p in Refl

mult_n_Sk : (n, k : Nat) -> n * (S k) = n + (n * k)
mult_n_Sk Z k = Refl
mult_n_Sk (S j) k =
    rewrite mult_n_Sk j k in
        rewrite plus_swap k j (mult j k) in
            Refl

total
mult_comm : (m, n : Nat) -> m * n = n * m
mult_comm Z n = rewrite mult_0_r n in Refl
mult_comm (S k) n = rewrite mult_n_Sk n k in rewrite mult_comm k n in Refl

total
le_refl : (n : Nat) -> lte n n = True
le_refl Z = Refl
le_refl (S k) = rewrite le_refl k in Refl

zero_nbeq_S : (n : Nat) -> 0 == (S n) = False
zero_nbeq_S n = Refl

andb_false_r : (b : Bool) -> b && False = False
andb_false_r False = Refl
andb_false_r True = Refl

plus_ble_compat_l : (n, m, p : Nat) -> lte n m = True -> lte (p + n) (p + m) = True
plus_ble_compat_l n m Z prf = prf
plus_ble_compat_l n m (S k) prf = rewrite plus_ble_compat_l n m k prf in Refl

S_nbeq_0 : (n : Nat) -> (S n) == 0 = False
S_nbeq_0 n = Refl

mult_1_l : (n : Nat) -> 1 * n = n
mult_1_l n = rewrite plus_0_r n in Refl

all3_spec : (b, c : Bool) -> (b && c) || ((not b) || (not c)) = True
all3_spec False c = Refl
all3_spec True False = Refl
all3_spec True True = Refl

total
mult_plus_distr_r : (n, m, p : Nat) -> (n + m) * p = (n * p) + (m * p)
mult_plus_distr_r Z m p = Refl
mult_plus_distr_r (S k) m p =
    rewrite mult_plus_distr_r k m p in
        rewrite plus_assoc p (k * p) (m * p) in
            Refl

total
mult_assoc : (n, m, p : Nat) -> n * (m * p) = (n * m) * p
mult_assoc Z m p = Refl
mult_assoc (S k) m p =
    rewrite mult_assoc k m p in
        rewrite mult_plus_distr_r m (mult k m) p in
            Refl

total
beq_nat_refl : (n : Nat) -> True = n == n
beq_nat_refl Z = Refl
beq_nat_refl (S k) = rewrite beq_nat_refl k in Refl

total
plus_swap' : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
plus_swap' n m p =
    rewrite plus_assoc n m p in
        rewrite plus_assoc m n p in
            rewrite plus_comm n m in
                Refl

data Bin : Type where
    Z : Bin
    Odd : Bin -> Bin
    Even : Bin -> Bin

incr : Bin -> Bin
incr Z = Odd Z
incr b@(Odd x) = Even b
incr b@(Even x) = Odd b

binToNat : Bin -> Nat
binToNat Z = Z
binToNat (Odd x) = 1 + binToNat x
binToNat (Even x) = 1 + binToNat x

bin_to_nat_pres_incr : (b : Bin) -> S (binToNat b) = binToNat $ incr b 
bin_to_nat_pres_incr Z = Refl
bin_to_nat_pres_incr (Odd x) = Refl
bin_to_nat_pres_incr (Even x) = Refl

natToBin : Nat -> Bin
natToBin Z = Z
natToBin (S (S k)) = Even (natToBin k)
natToBin (S k) = Odd (natToBin k)

nat_conv_full_cycle : (n : Nat) -> binToNat $ natToBin n = n
nat_conv_full_cycle Z = Refl
nat_conv_full_cycle (S k) = ?nat_conv_full_cycle_rhs_2
