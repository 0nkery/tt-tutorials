%default total

identity_fn_applied_twice : (f : Bool -> Bool) -> ((x : Bool) -> f x = x) -> (b : Bool) -> f (f b) = b
identity_fn_applied_twice f g b = rewrite g b in g b

negation_fn_applied_twice : (f : Bool -> Bool) -> ((x : Bool) -> f x = not x) -> (b : Bool) -> f (f b) = b
negation_fn_applied_twice f g False = rewrite g (f False) in rewrite g False in Refl
negation_fn_applied_twice f g True = rewrite g (f True) in rewrite g True in Refl

andb_eq_orb : (b, c : Bool) -> (b && c = b || c) -> b = c
andb_eq_orb False False prf = Refl
andb_eq_orb False True Refl impossible
andb_eq_orb True False Refl impossible
andb_eq_orb True True prf = Refl

data Bin : Type where
    Z : Bin
    Odd : Bin -> Bin
    Even : Bin -> Bin

incr : Bin -> Bin
incr Z = Odd Z
incr (Odd x) = Even x
incr b@(Even x) = Odd b

binToNat : Bin -> Nat
binToNat Z = Z
binToNat (Odd x) = S (binToNat x)
binToNat (Even x) = S (S (binToNat x))

bin_to_nat_pres_incr : (b : Bin) -> binToNat $ incr b = S (binToNat b)
bin_to_nat_pres_incr Z = Refl
bin_to_nat_pres_incr (Odd x) = Refl
bin_to_nat_pres_incr (Even x) = Refl

natToBin : (n : Nat) -> Bin
natToBin Z = Z
natToBin (S k) = incr $ natToBin k

bin_to_nat_reverse_eq : (n : Nat) -> binToNat $ natToBin n = n
bin_to_nat_reverse_eq Z = Refl
bin_to_nat_reverse_eq (S k) =
    rewrite bin_to_nat_pres_incr (natToBin k) in
        rewrite bin_to_nat_reverse_eq k in
            Refl

nat_to_bin_reverse_eq : (b : Bin) -> natToBin $ binToNat b = b
nat_to_bin_reverse_eq Z = Refl
nat_to_bin_reverse_eq k = rewrite nat_to_bin_reverse_eq k in Refl
