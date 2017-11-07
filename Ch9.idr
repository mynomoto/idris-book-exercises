import Data.Vect

removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) -> Vect n a
removeElem value (value :: ys) Here = ys
removeElem {n = Z} value (y :: []) (There later) = absurd later
removeElem {n = (S k)} value (y :: ys) (There later) = y :: removeElem value ys later

data ElemList : a -> List a -> Type where
  HereList : ElemList x (x :: xs)
  ThereList : (later : ElemList x xs) -> ElemList x (y :: xs)

notInNil : ElemList value [] -> Void
notInNil HereList impossible
notInNil (ThereList _) impossible

notInTail : (notThere : ElemList value xs -> Void) -> (notHere : (value = x) -> Void) -> ElemList value (x :: xs) -> Void
notInTail notThere notHere HereList = notHere Refl
notInTail notThere notHere (ThereList later) = notThere later

isElem : DecEq a => (value : a) -> (xs : List a) -> Dec (ElemList value xs)
isElem value [] = No notInNil
isElem value (x :: xs) = case decEq value x of
                              Yes Refl => Yes HereList
                              No notHere => case isElem value xs of
                                                 (Yes prf) => Yes (ThereList prf)
                                                 (No notThere) => No (notInTail notThere notHere)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notInEmpty : Last [] value -> Void
notInEmpty LastOne impossible
notInEmpty (LastCons _) impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast _ (LastCons LastOne) impossible
notLast _ (LastCons (LastCons _)) impossible


notIsLast : (contra1 : Last xs value -> Void) -> (contra : (xs = []) -> Void) -> Last (x :: xs) value -> Void
notIsLast contra1 contra LastOne = contra Refl
notIsLast contra1 contra (LastCons prf) = contra1 prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInEmpty
isLast (x :: xs) value = case decEq xs [] of
                              (Yes Refl) => (case decEq x value of
                                                  (Yes Refl) => Yes LastOne
                                                  (No contra) => No (notLast contra))
                              (No contra) => (case isLast xs value of
                                                   (Yes prf) => Yes (LastCons prf)
                                                   (No contra1) => No (notIsLast contra1 contra))
