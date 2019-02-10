data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : Vect k a -> Vect (S k) a

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                            Nothing => Nothing
                            Just eq => Just (cong eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case decEq m len of
                                Yes Refl => Just input
                                No contra => Nothing

sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons Refl = Refl

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq : (x1 : a) -> (x2 : a) -> (x3 : a) -> Type where
    Same : (x : a) -> ThreeEq x x x 

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (Same z) = Same (S z)
