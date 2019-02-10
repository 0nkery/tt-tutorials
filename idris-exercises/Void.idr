twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSucc : (x : Nat) -> x = S x -> Void
valueNotSucc _ Refl impossible
