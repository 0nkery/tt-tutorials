data Last : List a -> a -> Type where
    LastOne : Last [value] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

last123 : Last [1, 2, 3] 3
last123 = LastCons (LastCons LastOne)

notInNil : Last [] value -> Void
notInNil LastOne impossible
notInNil (LastCons _) impossible

notLast : (notHere : (value = x) -> Void) -> Last [x] value -> Void
notLast notHere LastOne = notHere Refl
notLast notHere (LastCons prf) = notInNil prf

notLastInTail : (notLastPrf : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notLastInTail notLastPrf (LastCons prf) = notLastPrf prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInNil
isLast (x :: []) value =
    case decEq value x of
        Yes Refl => Yes LastOne
        No notHere => No (notLast notHere)
isLast (x :: (y :: xs)) value =
    case isLast (y :: xs) value of
        Yes prf => Yes (LastCons prf)
        No notLastPrf => No (notLastInTail notLastPrf)
