plusId : (n, m, o : Nat) -> (n = m) -> (m = o) -> n + m = m + o
plusId n m o prf prf1 = rewrite prf in rewrite prf1 in Refl

mult0Plus : (n, m : Nat) -> (0 + n) * m = n * (0 + m)
mult0Plus n m = Refl

mult_S_1 : (n, m : Nat) -> (m = S n) -> m * (1 + n) = m * m
mult_S_1 n m prf = rewrite prf in Refl

andb_true_elim_2 : (b, c : Bool) -> b && c = True -> c = True
andb_true_elim_2 False False Refl impossible
andb_true_elim_2 True False Refl impossible
andb_true_elim_2 False True prf = Refl
andb_true_elim_2 True True prf = Refl

zero_nbeq_plus_1 : (n : Nat) -> 0 == (n + 1) = False
zero_nbeq_plus_1 Z = Refl
zero_nbeq_plus_1 (S k) = Refl
