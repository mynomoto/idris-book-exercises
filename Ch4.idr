import Data.Vect

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x (Node left val right) = case compare x val of
                                    LT => Node (insert x left) val right
                                    EQ => Node left val right
                                    GT => Node left val (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree xs = foldr insert Empty xs

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node x y z) = (treeToList x) ++ [y] ++ (treeToList z)

data Expr = Val Int
          | Add Expr Expr
          | Subt Expr Expr
          | Mult Expr Expr

evaluate : Expr -> Int
evaluate (Val x) = x
evaluate (Add x y) = (evaluate x) + (evaluate y)
evaluate (Subt x y) = (evaluate x) - (evaluate y)
evaluate (Mult x y) = (evaluate x) * (evaluate y)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe x Nothing = x
maxMaybe (Just x) (Just y) = Just (max x y)

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

area : Shape -> Double
area (Triangle base height) = 0.5 * base * height
area (Rectangle length height) = length * height
area (Circle radius) = pi * radius * radius

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive t@(Triangle x y)) = Just (area t)
biggestTriangle (Primitive x) = Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3))
                   (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3))
                   (Primitive (Circle 4))

data PowerSource = Petrol | Pedal | Eletric

data Vehicle : PowerSource -> Type where
          Bicycle : Vehicle Pedal
          Unicycle : Vehicle Pedal
          Car : (fuel : Nat) -> Vehicle Petrol
          Bus : (fuel : Nat) -> Vehicle Petrol
          Motorcycle : (fuel : Nat) -> Vehicle Petrol
          EletricCar : (charge : Nat) -> Vehicle Eletric
          Tram : (charge : Nat) -> Vehicle Eletric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2
wheels (EletricCar charge) = 4
wheels (Tram charge) = 6

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50

recharge : Vehicle Eletric -> Vehicle Eletric
recharge (EletricCar charge) = EletricCar 2000
recharge (Tram charge) = Tram 4000

vectTake : (s : Fin (S n)) -> Vect n a -> Vect (cast s) a
vectTake FZ xs = []
vectTake (FS x) (y :: xs) = y :: vectTake x xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n = Z} pos xs ys = Nothing
sumEntries {n = (S k)} pos xs ys = case pos > (cast k) of
                            False => let r = (restrict k pos)
                                         ix = (index r xs)
                                         iy = (index r ys) in
                                         Just (ix + iy)
                            True => Nothing
