import Data.Primitives.Views
import System

%default total

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

run : Fuel -> InfIO -> IO ()
run (More fuel) (Do action cont) =
    do
        res <- action
        run fuel (cont res)
run Dry p = putStrLn "Out of fuel"
