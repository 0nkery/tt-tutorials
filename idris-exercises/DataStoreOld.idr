import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType SChar = Char
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newItem =
    MkData schema _ (addToData items) 
    where
        addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
        addToData [] = [newItem]
        addToData (x :: xs) = x :: addToData xs

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = SChar} item = show item
display {schema = (y .+. z)} (itemL, itemR) = display itemL ++ ", " ++ display itemR

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store =
    let store_items = items store in
        case integerToFin pos (size store) of
            Nothing => Just ("Out of range\n", store)
            Just id => Just (display (index id (items store)) ++ "\n", store)

data Command : Schema -> Type where
    SetSchema : (newSchema : Schema) -> Command schema
    Add : SchemaType schema -> Command schema
    Get : Maybe Integer -> Command schema
    Quit : Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
    where
        getQuoted : List Char -> Maybe (String, String)
        getQuoted ('"' :: xs) = case span (/= '"') xs of
                                    (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                                    _ => Nothing
        getQuoted _ = Nothing

parsePrefix SInt input = case span isDigit input of
                        ("", rest) => Nothing
                        (num, rest) => Just (cast num, ltrim rest)

parsePrefix SChar input = getChar (unpack input)
    where
        getChar : List Char -> Maybe (Char, String)
        getChar (char :: ' ' :: rest) = Just (char, pack rest)
        getChar (char :: []) = Just (char, "")
        getChar _ = Nothing    

parsePrefix (schemaL .+. schemaR) input =
    do
        (lVal, input') <- parsePrefix schemaL input
        (rVal, input'') <- parsePrefix schemaR input'
        Just ((lVal, rVal), input'')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                Just (res, "") => Just res
                                Just _ => Nothing
                                Nothing => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) =
    case xs of
        [] => Just SString
        _ =>
            do
                restSchema <- parseSchema xs
                Just (SString .+. restSchema)
parseSchema ("Int" :: xs) =
    case xs of
        [] => Just SInt
        _ =>
            do
                restSchema <- parseSchema xs
                Just (SInt .+. restSchema)
parseSchema ("Char" :: xs) =
    case xs of
        [] => Just SChar
        _ =>
            do
                restSchema <- parseSchema xs
                Just (SChar .+. restSchema)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" rest =
    do
        restOk <- parseBySchema schema rest
        Just (Add restOk)
parseCommand schema "get" "" = Just (Get Nothing)
parseCommand schema "get" val =
    case all isDigit (unpack val) of
        False => Nothing
        True => Just (Get $ Just (cast val))
parseCommand schema "schema" val =
    do
        schemaok <- parseSchema (words val)
        Just (SetSchema schemaok)
parseCommand schema "quit" "" = Just Quit
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                        (cmd, args) => parseCommand schema cmd (ltrim args)

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                            Z => Just (MkData schema _ [])
                            S k => Nothing

showItems : Vect len (SchemaType schema) -> String
showItems [] = ""
showItems (item :: items') = display item ++ "\n" ++ showItems items'

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input
    = case parse (schema store) input of
            Nothing => Just ("Invalid command\n", store)
            Just (Add item) =>
                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
            Just (Get Nothing) => Just (showItems $ items store, store)
            Just (Get $ Just pos) => getEntry pos store
            Just (SetSchema schema') =>
                case setSchema store schema' of
                    Nothing => Just ("Can't update schema\n", store)
                    Just store' => Just ("OK\n", store')
            Just Quit => Nothing

main : IO ()
main = replWith (MkData (SString .+. SInt) _ []) "Command: " processInput