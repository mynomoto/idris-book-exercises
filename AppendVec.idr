import Data.Vect

%default total

append1 : Vect n elem -> Vect m elem -> Vect (n + m) elem
append1 [] ys = ys
append1 (x :: xs) ys = x :: append1 xs ys

appendNil : Vect m elem -> Vect (plus m 0) elem
appendNil {m} xs = rewrite plusZeroRightNeutral m in xs

appendXs : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
appendXs {m} {k} xs = rewrite sym
                      (plusSuccRightSucc m k) in xs

append2 : Vect n elem -> Vect m elem -> Vect (m + n) elem
append2 [] ys = appendNil ys
append2 (x :: xs) ys = appendXs (x :: append2 xs ys)
