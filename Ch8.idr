%default total

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat' Z Z = Just (Same 0)
checkEqNat' Z (S k) = Nothing
checkEqNat' (S k) Z = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                              Nothing => Nothing
                              (Just eq) => Just (sameS _ _ eq)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just prf) => Just (cong prf)

exactLength' : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength' {m} len input = case checkEqNat m len of
                                 Nothing => Nothing
                                 (Just Refl) => Just input

same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons Refl = Refl

same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  Teq : (x : a) -> ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (Teq z) = Teq (S z)
