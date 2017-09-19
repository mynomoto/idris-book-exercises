module Main
import Data.Vect

%default total

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)


addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem = MkData schema _ (addToData items)
  where
    addToData : Vect oldsize (SchemaType schema) -> Vect (S oldsize) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command : Schema -> Type where
  SetSchema : (newschema : Schema) -> Command schema
  Add: SchemaType schema -> Command schema
  Get: Integer -> Command schema
  Size: Command schema
  Quit: Command schema

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

parsePrefix (schemal .+. schemar) input = case parsePrefix schemal input of
                                               Nothing => Nothing
                                               (Just (lval, input')) => case parsePrefix schemar input' of
                                                                             Nothing => Nothing
                                                                             (Just (rval, input'')) => Just ((lval, rval), input'')

parseBySchema : (schema : Schema) ->  String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
                                  Nothing => Nothing
                                  Just (res, "") => Just res
                                  Just _ => Nothing

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: []) = Just SString
parseSchema ("String" :: xs) = case parseSchema xs of
                                    Nothing => Nothing
                                    Just xs_schema => Just (SString .+. xs_schema)
parseSchema ("Int" :: []) = Just SInt
parseSchema ("Int" :: xs) = case parseSchema xs of
                                    Nothing => Nothing
                                    Just xs_schema => Just (SInt .+. xs_schema)
parseSchema _ = Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" str = case parseBySchema schema str of
                                     Nothing => Nothing
                                     (Just str_ok) => Just (Add str_ok)
-- parseCommand "search" str = Just (Search str)
parseCommand schema "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "size" "" = Just Size
parseCommand schema "schema" str = case parseSchema (words str) of
                                        Nothing => Nothing
                                        Just schema_ok => Just (SetSchema schema_ok)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (x .+. y)} (item1, item2) = display item1 ++ ", " ++ display item2

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just id => Just ((display (index id store_items)) ++ "\n", store)

{-
searchEntry : (query : String) -> (store : DataStore) -> Maybe (String, DataStore)
searchEntry query store = let store_items = items store
                              filtered = foldl (\acc, item => if Strings.isInfixOf query item
                                                                then (length acc, item) :: acc
                                                                else acc) [] store_items in
                              (case reverse filtered of
                                    [] => Just ("Nothing found\n", store)
                                    xs => let showItem = map (\(idx, it) => (show idx) ++ ": " ++ it) xs
                                              s = (concat (intersperse "\n" showItem)) in
                                              Just((s ++ "\n"), store))
-}

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
                         Z => Just (MkData schema _ [])
                         (S k) => Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                              Nothing => Just ("Invalid command\n", store)
                              Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              Just (Get pos) => getEntry pos store
                              -- Just (Search query) => searchEntry query store
                              Just Size => Just("Size " ++ show (size store) ++ "\n", store)
                              Just (SetSchema schema') => case setSchema store schema' of
                                                               Nothing => Just ("Can't update schema\n", store)
                                                               Just store' => Just ("Ok\n", store')
                              Just Quit => Nothing

partial
main : IO ()
main = replWith (MkData (SString .+. SString .+. SInt) _ []) "Command: " processInput
