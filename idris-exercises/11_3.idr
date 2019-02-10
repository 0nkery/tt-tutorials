data Command : Type -> Type where
    PutStr : String -> Command ()
    GetLine : Command String
    ReadFile : String -> Command (Either FileError String)
    WriteFile : String -> String -> Command (Either FileError ())

    Pure : ty -> Command ty
    Bind : Command a -> (a -> Command b) -> Command b

namespace CommandDo
    (>>=) : Command a -> (a -> Command b) -> Command b
    (>>=) = Bind

total
runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile fileName) = readFile fileName
runCommand (WriteFile fileName contents) = writeFile fileName contents
runCommand (Pure val) = pure val
runCommand (Bind c f) = do res <- runCommand c
                           runCommand (f res)

data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
    (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
    (>>=) = Do

data ShellCommand : Type -> Type where
    Cat : Command String -> ShellCommand (Command String)
    Copy : String -> String -> Command () -> ShellCommand (Command ())
    Exit : ShellCommand ()

--             ("copy" :: source :: dest :: []) =>
--                 do
--                     Right contents <- ReadFile source
--                     Right () <- WriteFile dest contents
--                     Pure ()
            -- ("exit" :: []) =>
            --     do

shell : ConsoleIO String
shell =
    do
        PutStr "$ "
        command <- GetLine
        let command = words command
        case command of
            ("cat" :: filename :: []) =>
                do
                    Right contents <- ReadFile filename
                    PutStr contents
                    shell

            ("copy" :: src :: dst :: []) =>
                do
                    Right contents <- ReadFile src
                    Right () <- WriteFile dst contents
                    PutStr "Copying complete!"
                    shell

            ("exit" :: []) =>
                Quit "Bye-bye!"
