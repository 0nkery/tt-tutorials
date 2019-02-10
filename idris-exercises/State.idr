import Control.Monad.State

increase : Nat -> State Nat ()
increase inc =
    do
        current <- get
        put (current + inc)

update : (stateType -> stateType) -> State stateType ()
update f =
    do
        state <- get
        put (f state)

increase' : Nat -> State Nat ()
increase' inc = update (+inc)
