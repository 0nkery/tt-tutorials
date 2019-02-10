import Data.Vect

plus' : Nat -> Nat -> Nat
plus' Z m = m
plus' (S k) m = S (plus' k m)

fourEq : 4 = 4
fourEq = Refl

twoPlusTwoEqFour : 2 + 2 = 4
twoPlusTwoEqFour = Refl

plusReducesZ : (m : Nat) -> plus' Z m = m
plusReducesZ m = Refl

plusReducesSk : (k, m : Nat) -> plus' (S k) m = S (plus' k m)
plusReducesSk k m = Refl

vectEqLength : (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> n = m
vectEqLength xs xs Refl = Refl

natInduction : (p : Nat -> Type) -> (p Z) -> ((k : Nat) -> p k -> p (S k)) -> (x : Nat) -> p x
natInduction p pZ pS Z = pZ
natInduction p pZ pS (S k) = pS k (natInduction p pZ pS k)

plusInd : Nat -> Nat -> Nat
plusInd n m = natInduction (\x => Nat) m (\k, kRec => S kRec) n

-- plusCommutesZ : m = plus' m 0
-- plusCommutesZ {m = Z} = Refl
-- plusCommutesZ {m = (S k)} =
--     let rec = plusCommutesZ {m = k} in cong rec

-- plusCommutesSk : (k : Nat) -> (m : Nat) -> S (plus' m k) = plus' m (S k)
-- plusCommutesSk k Z = Refl
-- plusCommutesSk k (S j) = cong $ plusCommutesSk k j

-- plusCommutes : (n, m : Nat) -> plus' n m = plus' m n
-- plusCommutes Z m = plusCommutesZ
-- plusCommutes (S k) m = rewrite plusCommutes k m in plusCommutesSk k m

-- plusCommutes : (n, m : Nat) -> plus' n m = plus' m n
-- plusCommutes n m = natInduction (\x => plus' x m = plus' m x) ?rest

plusAssoc : (n, m, p : Nat) -> plus' n (plus' m p) = plus' (plus' n m) p
