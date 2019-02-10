import Control.Monad.State

data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String
testTree =
    Node (Node (Node Empty "Jim" Empty) "Fred"
    (Node Empty "Sheila" Empty)) "Alice"
    (Node Empty "Bob" (Node Empty "Eve" Empty))

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left val right) = flatten left ++ val :: flatten right

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) =
    do
        leftLabelled <- treeLabelWith left
        (this :: rest) <- get
        put rest
        rightLabelled <- treeLabelWith right
        pure (Node leftLabelled (this, val) rightLabelled)

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = evalState (treeLabelWith tree) [1..]

countEmpty : Tree a -> State Nat ()
countEmpty Empty =
    do
        count <- get
        put (S count)
countEmpty (Node left val right) =
    do
        countEmpty left
        countEmpty right

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty =
    do
        (empties, nodes) <- get
        put ((S empties), nodes)
countEmptyNode (Node left val right) =
    do
        countEmptyNode left
        (empties, nodes) <- get
        put (empties, (S nodes))
        countEmptyNode right
