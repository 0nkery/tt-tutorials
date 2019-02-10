data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Absolute (Expr num)

eval : (Neg num, Abs num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Absolute x) = abs (eval x)

Num ty => Num (Expr ty) where
    (+) = Add
    (*) = Mul
    fromInteger = Val . fromInteger

Neg ty => Neg (Expr ty) where
    negate x = 0 - x
    (-) = Sub

Show ty => Show (Expr ty) where
    show (Val x) = show x
    show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
    show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
    show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
    show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
    show (Absolute x) = "|" ++ show x ++ "|"

(Neg ty, Integral ty, Abs ty, Eq ty) => Eq (Expr ty) where
    (==) x y = eval x == eval y

(Neg ty, Integral ty, Abs ty) => Cast (Expr ty) ty where
     cast expr = eval expr

Functor Expr where
    map f (Val x) = Val $ f x
    map f (Add x y) = Add (map f x) (map f y)
    map f (Sub x y) = Sub (map f x) (map f y)
    map f (Mul x y) = Mul (map f x) (map f y)
    map f (Div x y) = Div (map f x) (map f y)
    map f (Absolute x) = Absolute (map f x)
