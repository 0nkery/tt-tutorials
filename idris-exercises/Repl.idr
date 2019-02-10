repl' : (prompt : String) -> (onInput : String -> String) -> IO ()
repl' prompt onInput =
    do
        putStr prompt
        input <- getLine
        let output = onInput input
        putStrLn output
        repl' prompt onInput

replWith' : (state : a) -> (prompt : String) -> (onInput : a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt onInput =
    do
        putStr prompt
        input <- getLine
        let next = onInput state input
        case next of
            Nothing => pure ()
            (Just (output, newState)) =>
                do
                    putStrLn output
                    replWith' newState prompt onInput
