%language TypeProviders

strToType : String -> Type
strToType "Int" = Int
strToType _ = Nat

fromFile : String -> IO (Provider Type)
fromFile fname = do Right str <- readFile fname
                      | Left err =>
                            do
                                putStrLn "Failed to load file"
                                pure (Provide Void)
                    pure (Provide (strToType (trim str)))

%provide (T1 : Type) with fromFile "theType"

foo : T1
foo = 2
