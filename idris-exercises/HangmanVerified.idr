import Data.Vect

%default total

data GameState : Type where
    NotRunning : GameState
    Running : (guesses : Nat) -> (letters : Nat) -> GameState

letters : String -> List Char
letters = nub . map toUpper . unpack

data GuessResult = Correct | Incorrect

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    NewGame : (word : String) ->
              GameCmd () NotRunning (const (Running 6 (length (letters word))))
    Won : GameCmd () (Running (S guesses) 0) (const NotRunning)
    Lost : GameCmd () (Running 0 (S guesses)) (const NotRunning)

    Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters))
        (\check =>
            case check of
                Correct => Running (S guesses) letters
                Incorrect => Running guesses (S letters))

    ShowState : GameCmd () state (const state)
    Message : String -> GameCmd () state (const state)
    ReadGuess : GameCmd Char state (const state)

    Pure : (res : ty) -> GameCmd ty (stateFn res) stateFn
    (>>=) : GameCmd a state1 state2Fn ->
            ((res : a) -> GameCmd b (state2Fn res) state3Fn) ->
            GameCmd b state1 state3Fn

namespace Loop
    data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
        (>>=) : GameCmd a state1 state2Fn ->
                ((res : a) -> Inf (GameLoop b (state2Fn res) state3Fn)) ->
                GameLoop b state1 state3Fn
        Exit : GameLoop () NotRunning (const NotRunning)

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} =
    do
        ShowState
        g <- ReadGuess
        ok <- Guess g
        case ok of
            Correct =>
                case letters of
                    Z =>
                        do
                            Won
                            ShowState
                            Exit
                    (S k) =>
                        do
                            Message "Correct"
                            gameLoop
            Incorrect =>
                case guesses of
                    Z =>
                        do
                            Lost
                            ShowState
                            Exit
                    (S k) =>
                        do
                            Message "Incorrect"
                            gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman =
    do
        NewGame "testing"
        gameLoop

data Game : GameState -> Type where
    GameStart : Game NotRunning
    GameWon : (word : String) -> Game NotRunning
    GameLost : (word : String) -> Game NotRunning
    InProgress : (word : String) -> (guesses : Nat) ->
                (missing : Vect letters Char) ->
                Game (Running guesses letters)  

Show (Game g) where
    show GameStart = "Starting"
    show (GameWon word) = "Game won: word was " ++ word
    show (GameLost word) = "Game lost: word was " ++ word
    show (InProgress word guesses missing) =
        "\n" ++ pack (map hideMissing (unpack word)) ++
        "\n" ++ show guesses ++ " guesses left"
        where
            hideMissing : Char -> Char
            hideMissing c = if c `elem` missing then '-' else c

data Fuel = Dry | More (Lazy Fuel)

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
    OK : (res : ty) -> Game (outStateFn res) -> GameResult ty outStateFn
    OutOfFuel : GameResult ty outStateFn

ok : (res : ty) -> Game $ outStateFn res ->
    IO $ GameResult ty outStateFn
ok res st = pure $ OK res st

runCmd : Fuel -> Game inState -> GameCmd ty inState outStateFn ->
        IO (GameResult ty outStateFn)
runCmd fuel state (NewGame word) = ok () (InProgress (toUpper word) _ (fromList $ letters word))
runCmd fuel (InProgress word _ missing) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ missing) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c) =
    case isElem c missing of
        Yes prf => ok Correct (InProgress word _ (dropElem missing prf))
        No contra => ok Incorrect (InProgress word _ missing)
runCmd fuel state ShowState =
    do
        printLn state
        ok () state
runCmd fuel state (Message msg) =
    do
        putStrLn msg
        ok () state
runCmd (More fuel) state ReadGuess =
    do
        putStr "Guess: "
        input <- getLine
        case unpack input of
            [x] =>
                if isAlpha x
                    then ok (toUpper x) state
                    else
                        do
                            putStrLn "Invalid input"
                            runCmd fuel state ReadGuess
            _ =>
                do
                    putStrLn "Invalid input"
                    runCmd fuel state ReadGuess
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) =
    do
        OK cmdRes newState <- runCmd fuel state cmd
            | OutOfFuel => pure OutOfFuel
        runCmd fuel newState (next cmdRes)
runCmd Dry _ _ = pure OutOfFuel

run : Fuel -> Game inState -> GameLoop ty inState outStateFn ->
    IO (GameResult ty outStateFn)
run Dry _ _ = pure OutOfFuel
run (More fuel) state (cmd >>= next) =
    do
        OK cmdRes newState <- runCmd fuel state cmd
            | OutOfFuel => pure OutOfFuel
        run fuel newState (next cmdRes)
run (More fuel) state Exit = ok () state

%default partial

forever : Fuel
forever = More forever

main : IO ()
main =
    do
        run forever GameStart hangman
        pure ()
