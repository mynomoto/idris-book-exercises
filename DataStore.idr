module DataStore

import Data.Vect

%default total

infixr 5 .+.

public export
data Schema = SString
            | SInt
            | SChar
            | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SChar = Char
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  Snil : StoreView empty
  Sadd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelper : (items : Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelper [] = Snil
storeViewHelper (x :: xs) = Sadd (storeViewHelper xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelper items
