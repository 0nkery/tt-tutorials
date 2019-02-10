data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

loopPrint : String -> InfIO
loopPrint msg =
    do
        putStrLn msg
        loopPrint msg

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do action cont) =
    do
        res <- action
        run fuel (cont res)
run Dry p = putStrLn "Out of fuel"
