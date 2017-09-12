module Main
import Data.Vect

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
  Add: SchemaType schema -> Command schema
  Get: Integer -> Command schema
  Size: Command schema
  Quit: Command schema

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" str = Just (Add (?parseBySchema str))
-- parseCommand "search" str = Just (Search str)
parseCommand schema "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "size" "" = Just Size
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just id => Just ((display (schema store)) (index id store_items) ++ "\n", store)

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

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse (schema store) inp of
                              Nothing => Just ("Invalid command\n", store)
                              Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              Just (Get pos) => getEntry pos store
                              -- Just (Search query) => searchEntry query store
                              Just Size => Just("Size " ++ show (size store) ++ "\n", store)
                              Just Quit => Nothing

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
