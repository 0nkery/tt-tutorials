module Main

import System

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
    then pure (Just (cast input))
    else pure Nothing

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses =
    do
        putStr ("Number (attempt #" ++ (show guesses) ++ "): ")
        Just num <- readNumber
            | Nothing =>
                do
                    putStrLn "Invalid input"
                    guess target guesses

        case compare num target of
            LT =>
                do
                    putStrLn "Too low"
                    guess target (S guesses)
            EQ => putStrLn "Correct!"
            GT =>
                do
                    putStrLn "Too high!"
                    guess target (S guesses)

main : IO ()
main =
    do
        randomVal <- time
        let target = randomVal - 1529902000
        guess (cast target) 0
