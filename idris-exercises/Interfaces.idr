occurences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurences item [] = 0
occurences item (value :: values) = case value == item of
                                        False => occurences item values
                                        True => 1 + occurences item values

data Matter = Solid | Liquid | Gas

Eq Matter where
    (==) Solid Solid = True
    (==) Liquid Liquid = True
    (==) Gas Gas = True
    (==) _ _ = False

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
    (==) Empty Empty = True
    (==) (Node left el right) (Node left' el' right') =
        left == left' && el == el' && right == right'
    (==) _ _ = False

Functor Tree where
    map func Empty = Empty
    map func (Node left el right) =
        Node (map func left) (func el) (map func right)

Foldable Tree where
    foldr func acc Empty = acc
    foldr func acc (Node left el right) =
        let leftFold = foldr func acc left
            rightFold = foldr func leftFold right in
            func el rightFold

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
    (==) (Triangle x z) (Triangle y w) = x == y && z == w
    (==) (Rectangle x z) (Rectangle y w) = x == y && z == w
    (==) (Circle x) (Circle y) = x == y
    (==) _ _ = False

area : Shape -> Double
area (Triangle x y) = x * y * 0.5
area (Rectangle x y) = x * y
area (Circle x) = x * x * pi

Ord Shape where
    compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [
    Circle 3,
    Triangle 3 9,
    Rectangle 2 6,
    Circle 4,
    Rectangle 2 7
]