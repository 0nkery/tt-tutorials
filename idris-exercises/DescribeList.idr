data ListLast : List a -> Type where
    Empty : ListLast []
    NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : Show a => (input : List a) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) =
    "Non-empty, initial portion = " ++ show xs

total
listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) =
    case listLast xs of
        Empty => NonEmpty [] x
        NonEmpty ys y => NonEmpty (x :: ys) y

descibeListEnd : Show a => List a -> String
descibeListEnd xs = describeHelper xs (listLast xs)

descibeListEndWith : Show a => List a -> String
descibeListEndWith input with (listLast input)
  descibeListEndWith [] | Empty = "Empty"
  descibeListEndWith (xs ++ [x]) | (NonEmpty xs x) =
    "Non-empty, initial portion = " ++ show xs

myReverse : List a -> List a
myReverse input with (listLast input)
  myReverse [] | Empty = []
  myReverse (xs ++ [x]) | (NonEmpty xs x) = x :: myReverse xs
