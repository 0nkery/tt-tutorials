totalLen : List String -> Nat
totalLen xs = foldr (\el, acc  => length el  + acc) 0 xs  
