everyOther : Stream a -> Stream a
everyOther (val1 :: val2 :: xs) = val2 :: everyOther xs

squareRootApprox : (number : Double) -> (approx : Double) -> Stream Double
squareRootApprox number approx =
    let next = (approx + (number / approx)) / 2 in
        next :: squareRootApprox number next

squareRootBound : (max : Nat) -> (number : Double) -> (bound : Double)->
    (approxs : Stream Double) -> Double
squareRootBound Z number bound (value :: xs) = value
squareRootBound (S k) number bound (value :: xs) =
    if value * value - number < bound
        then value
        else squareRootBound k number bound xs

squareRoot : (num : Double) -> Double
squareRoot num = squareRootBound 100 num 0.00000000001 (squareRootApprox num num)
