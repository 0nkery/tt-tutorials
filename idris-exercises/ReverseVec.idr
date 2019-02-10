import Data.Vect

myReverse : Vect n el -> Vect n el
myReverse [] = []
myReverse (x :: xs) = reverseProof (myReverse xs ++ [x])
    where
        reverseProof : Vect (k + 1) el -> Vect (S k) el
        reverseProof {k} result = rewrite plusCommutative 1 k in result

appendNil : Vect m elem -> Vect (plus m 0) elem
appendNil {m} xs = rewrite plusZeroRightNeutral m in xs

appendXs : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
appendXs {m} {k} xs = rewrite sym (plusSuccRightSucc m k) in xs 

myAppend : Vect n elem -> Vect m elem -> Vect (m + n) elem
myAppend [] ys = appendNil ys
myAppend (x :: xs) ys = appendXs (x :: myAppend xs ys)

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

reverseProofXs : Vect ((S n) + len) el -> Vect (plus n (S len)) el
reverseProofXs {n} {len} result = rewrite sym (plusSuccRightSucc n len) in result

myReverse' : Vect n el -> Vect n el
myReverse' xs = reverse' [] xs where
    reverse' : Vect n el -> Vect m el -> Vect (n + m) el
    reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
    reverse' acc (x :: xs) = reverseProofXs (reverse' (x :: acc) xs)
