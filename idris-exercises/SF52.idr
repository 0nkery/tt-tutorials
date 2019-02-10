doit3times : (f : x -> x) -> (n : x) -> x
doit3times f = f . f . f

test_doit3times1 : doit3times (\n => n + 2) 3 = 9
test_doit3times1 = Refl

test_doit3times2 : doit3times (\b => not b) True = False
test_doit3times2 = Refl

fltr : (test : a -> Bool) -> (l : List a) -> List a
fltr test [] = []
fltr test (x :: xs) =
    if test x
        then x :: fltr test xs
        else fltr test xs

evenb : (n : Nat) -> Bool
evenb Z = True
evenb (S (S k)) = evenb k
evenb k = False

test_filter1 : fltr Main.evenb [1, 2, 3, 4] = [2, 4]
test_filter1 = Refl

test_filter2 : fltr (\l => length l == 1) [[1, 2], [3], [4], [5, 6, 7], [], [8]] = [[3], [4], [8]]
test_filter2 = Refl

oddb : (n : Nat) -> Bool
oddb Z = False
oddb (S Z) = True
oddb (S (S k)) = oddb k

count_oddmembers : (l : List Nat) -> Nat
count_oddmembers l = length $ fltr oddb l

test_count_oddmembers1 : count_oddmembers [1, 0, 3, 1, 4, 5] = 4
test_count_oddmembers1 = Refl

test_count_oddmembers2 : count_oddmembers [0, 2, 4] = 0
test_count_oddmembers2 = Refl

test_count_oddmembers3 : count_oddmembers [] = 0
test_count_oddmembers3 = Refl

test_anon_fn : doit3times (\n => mult n n) 2 = 256
test_anon_fn = Refl

filter_even_gt7 : (l : List Nat) -> List Nat
filter_even_gt7 = filter evenb . filter (\n => n > 7)

test_filter_even_gt7_1 : filter_even_gt7 [1, 2, 6, 9, 10, 3, 12, 8] = [10, 12, 8]
test_filter_even_gt7_1 = Refl

test_filter_even_gt7_2 : filter_even_gt7 [5, 2, 6, 19, 129] = []
test_filter_even_gt7_2 = Refl

partn : (test : a -> Bool) -> (l : List a) -> (List a, List a)
partn test [] = ([], [])
partn test (x :: xs) =
    let
        (ts, fs) = partn test xs
    in
        if test x
            then (x :: ts, fs)
            else (ts, x :: fs)

test_partition1 : partn Main.oddb [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4])
test_partition1 = Refl

test_partition2 : partn (\x => False) [5, 9, 0] = ([], [5, 9, 0])
test_partition2 = Refl

test_map1 : map (\x => 3 + x) [2, 0, 2] = [5, 3, 5]
test_map1 = Refl

test_map2 : map Main.oddb [2, 1, 2, 5] = [False, True, False, True]
test_map2 = Refl

test_map3 : map (\n => [evenb n, oddb n]) [2, 1, 2, 5] = [[True, False], [False, True], [True, False], [False, True]]
test_map3 = Refl
