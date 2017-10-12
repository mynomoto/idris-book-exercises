import Data.Vect

%default total

myReverse1 : Vect n elem -> Vect n elem
myReverse1 [] = []
myReverse1 {n = S k} (x :: xs) = rewrite plusCommutative 1 k in
                                         myReverse1 xs ++ [x]

reverseProof : Vect (k + 1) elem -> Vect (S k) elem
reverseProof {k} result = rewrite plusCommutative 1 k in result

myReverse2 : Vect n elem -> Vect n elem
myReverse2 [] = []
myReverse2 (x :: xs) = reverseProof (myReverse1 xs ++ [x])
