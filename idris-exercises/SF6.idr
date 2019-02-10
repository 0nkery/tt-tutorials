factorial : (n : Nat) -> Nat
factorial Z = 1
factorial n@(S k) = n * factorial k

testFactorial1 : factorial 3 = 6
testFactorial1 = Refl
testFactorial2 : factorial 5 = 10 * 12
testFactorial2 = Refl

beq_nat : (n, m : Nat) -> Bool
beq_nat Z Z = True
beq_nat Z (S j) = False
beq_nat (S k) Z = False
beq_nat (S k) (S j) = beq_nat k j

leb : (n, m : Nat) -> Bool
leb Z m = True
leb (S k) Z = False
leb (S k) (S j) = leb k j

blt_nat : (n, m : Nat) -> Bool
blt_nat n m = leb n m && not (beq_nat n m)

test_blt_nat_1 : blt_nat 2 2 = False
test_blt_nat_1 = Refl
test_blt_nat_2 : blt_nat 2 4 = True
test_blt_nat_2 = Refl
test_blt_nat_3 : blt_nat 4 2 = False
test_blt_nat_3 = Refl
