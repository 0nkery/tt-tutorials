data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String
testTree =
    Node (Node (Node Empty "Jim" Empty) "Fred"
    (Node Empty "Sheila" Empty)) "Alice"
    (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Stream labelType -> Tree a ->
                (Stream labelType, Tree (labelType, a))
treeLabelWith labels Empty = (labels, Empty)
treeLabelWith labels (Node left val right) =
    let
        (labelThis :: labelsLeft, leftLabelled) = treeLabelWith labels left
        (labelsRight, rightLabelled) = treeLabelWith labelsLeft right
    in
        (labelsRight, Node leftLabelled (labelThis, val) rightLabelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd (treeLabelWith [1..] tree)
