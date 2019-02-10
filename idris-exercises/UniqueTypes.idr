%language UniquenessTypes

data UList : Type -> UniqueType where
    Nil : UList a
    (::) : a -> UList a -> UList a

umap : (a -> b) -> UList a -> UList b
umap f [] = []
umap f (x :: xs) = f x :: umap f xs

dupList : UList a -> UList a
dupList [] = []
dupList (x :: xs) = x :: x :: dupList xs

-- data BadList : UniqueType -> Type where
--     Nil : {a : UniqueType} -> BadList a
--     (::) : {a : UniqueType} -> a -> BadList a -> BadList a

showU : Show a => Borrowed $ UList a -> String
showU xs = "[" ++ showU' xs ++ "]" where
    showU' : Borrowed $ UList a -> String
    showU' [] = ""
    showU' [x] = show x
    showU' (x :: xs) = show x ++ ", " ++ showU' xs

printAndUpdate : UList Int -> IO ()
printAndUpdate xs =
    do
        putStrLn $ showU xs
        let xs' = umap (* 2) xs
        putStrLn (showU xs')
