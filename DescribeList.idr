%default total

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty ys y) => NonEmpty (x :: ys) y

describeListEnd1 : List Int -> String
describeListEnd1 xs = describeHelper xs (listLast xs)

describeListEnd : List Int -> String
describeListEnd xs with (listLast xs)
  describeListEnd [] | Empty = "Empty"
  describeListEnd (ys ++ [x]) | (NonEmpty ys x) = "Non-empty, initial portion = " ++ show ys

partial
myReverse1 : List a -> List a
myReverse1 xs with (listLast xs)
  myReverse1 [] | Empty = []
  myReverse1 (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse1 ys
