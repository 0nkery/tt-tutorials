import Data.Vect

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem value {n = Z} (y :: []) (There later) = absurd later
removeElem value {n = (S k)} (y :: ys) (There later) = y :: removeElem value ys later

oneInVector : Elem 1 [1, 2, 3]
oneInVector = Here

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElemAuto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElemAuto value xs {prf} = removeElem value xs prf
