import Data.Vect

myLength : List a -> Nat
myLength [] = 0
myLength (x :: xs) = 1 + myLength xs

myReverse : List a -> List a
myReverse [] = []
myReverse (x :: xs) = (myReverse xs) ++ [x]

myListMap : (a -> b) -> List a -> List b
myListMap f [] = []
myListMap f (x :: xs) = (f x) :: myListMap f xs

myVectMap : (a -> b) -> Vect n a -> Vect n b
myVectMap f [] = []
myVectMap f (x :: xs) = f x :: myVectMap f xs

createEmpties : Vect m (Vect 0 a)
createEmpties = replicate _ []

transposeHelper : (x : Vect m a) ->  (xsTrans : Vect m (Vect len a)) -> Vect m (Vect (S len) a)
transposeHelper x xsTrans = zipWith (::) x xsTrans

transposeMat : Vect n (Vect m a) -> Vect m (Vect n a)
transposeMat [] = createEmpties
transposeMat (x :: xs) = let xsTrans = transposeMat xs in
                             transposeHelper x xsTrans

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix [] ys = ys
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

multHelper : Num a => (xs : Vect n (Vect m a)) -> (ysTrans : Vect p (Vect m a)) -> Vect n (Vect p a)
multHelper [] ysTrans = []
multHelper (x :: xs) ysTrans = let row = (map (\y => sum (zipWith (*) x y)) ysTrans) in
                                   row :: multHelper xs ysTrans

multMatrix : Num a => Vect n (Vect m a) -> Vect m (Vect p a) -> Vect n (Vect p a)
multMatrix xs ys = let ysTrans = transposeMat ys in
                       multHelper xs ysTrans
