import Data.Vect

PIN : Type
PIN = Vect 4 Char

data ATMState = Ready | CardInserted | Session

data PINCheck = CorrectPIN | IncorrectPIN

data HasCard : ATMState -> Type where
    HasCI : HasCard CardInserted
    HasSession : HasCard Session

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
    InsertCard : ATMCmd () Ready (const CardInserted)
    EjectCard : {auto prf : HasCard state} -> ATMCmd () state (const Ready)
    GetPIN : ATMCmd PIN CardInserted (const CardInserted)

    CheckPIN : PIN -> ATMCmd PINCheck CardInserted
                        (\check =>
                            case check of
                                CorrectPIN => Session
                                IncorrectPIN => CardInserted)
    GetAmount : ATMCmd Nat state (const state)

    Dispense : (amount : Nat) -> ATMCmd () Session (const Session)

    Message : String -> ATMCmd () state (const state)
    Pure : (res : ty) -> ATMCmd ty (stateFn res) stateFn
    (>>=) : ATMCmd a state1 state2Fn ->
            ((res : a) -> ATMCmd b (state2Fn res) state3Fn) ->
            ATMCmd b state1 state3Fn

atm : ATMCmd () Ready (const Ready)
atm =
    do
        InsertCard
        pin <- GetPIN
        cash <- GetAmount
        pinOK <- CheckPIN pin
        case pinOK of
            CorrectPIN =>
                do
                    Dispense cash
                    EjectCard
                    Message "Please remove your card and cash"
            IncorrectPIN =>
                do
                    Message "Incorrect PIN"
                    EjectCard

-- badATM : ATMCmd () state (const Ready)
-- badATM = EjectCard

testPIN : PIN
testPIN = ['1', '2', '3', '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z =
    do
        discard <- getLine
        pure []
readVect (S k) =
    do
        ch <- getChar
        chs <- readVect k
        pure (ch :: chs)

runATM : ATMCmd res inState outStateFn -> IO res
runATM InsertCard =
    do
        putStrLn "Please insert your card (press enter)"
        x <- getLine
        pure ()
runATM EjectCard  = putStrLn "Card ejected"
runATM GetPIN =
    do
        putStr "Enter PIN: "
        readVect 4
runATM (CheckPIN pin) =
    if pin == testPIN
        then pure CorrectPIN
        else pure IncorrectPIN
runATM GetAmount =
    do
        putStr "How much would you like? "
        x <- getLine
        pure (cast x)
runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) =
    do
        x' <- runATM x
        runATM (f x')
