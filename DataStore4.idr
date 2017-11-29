module Main
import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) -> (items : Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size' items') = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData size' items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Search String
             | Size
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" str = Just (Add str)
parseCommand "search" str = Just (Search str)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "quit" "" = Just Quit
parseCommand "size" "" = Just Size
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (pos : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry pos store = let store_items = items store in
                         case integerToFin pos (size store) of
                              Nothing => Just ("Out of range\n", store)
                              Just id => Just (index id store_items ++ "\n", store)

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

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store inp = case parse inp of
                              Nothing => Just ("Invalid command\n", store)
                              Just (Add item) => Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              Just (Get pos) => getEntry pos store
                              Just (Search query) => searchEntry query store
                              Just Size => Just("Size " ++ show (size store) ++ "\n", store)
                              Just Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
