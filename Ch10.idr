import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views
import DataStore
%default total

data TakeN : List a -> Type where
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             Exact n_xs => Exact (x :: n_xs)

partial
groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = [n_xs] ++ (groupByN n rest)

partial
halves : List a -> (List a, List a)
halves xs = let halfSize = div (size xs) 2 in
                case takeN halfSize xs of
                     Fewer => ([], xs)
                     Exact n_xs {rest} => (n_xs, rest)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix input1 input2 with (snocList input1)
  equalSuffix [] input2 | Empty = []
  equalSuffix (xs ++ [x]) input2 | (Snoc xsrec) with (snocList input2)
    equalSuffix (xs ++ [x]) [] | (Snoc xsrec) | Empty = []
    equalSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc xsrec) | (Snoc ysrec) =
      if x == y then (equalSuffix xs ys | xsrec | ysrec) ++ [x]
                else []

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort input with (splitRec input)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (xs ++ ys) | (SplitRecPair lrec rrec) = merge (mergeSort xs | lrec) (mergeSort ys | rrec)

toBinary : Nat -> String
toBinary k with (halfRec k)
  toBinary Z | HalfRecZ = ""
  toBinary (n + n) | (HalfRecEven rec) = (toBinary n | rec) ++ "0"
  toBinary (S (n + n)) | (HalfRecOdd rec) = (toBinary n | rec) ++ "1"

palindrome : Eq a => List a -> Bool
palindrome input with (vList input)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec) =
    if x == y then palindrome xs | rec
              else False

testStore : DataStore (SString .+. SInt)
testStore = addToStore ("First", 1) $
            addToStore ("Second", 2) $
            empty

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues input with (storeView input)
  getValues input | Snil = []
  getValues (addToStore (key, value) store) | (Sadd rec) = value :: getValues store | rec
