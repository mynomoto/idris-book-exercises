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

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in
                             Refl
myPlusCommutes (S k) m = rewrite (myPlusCommutes k m) in
                                 rewrite sym (plusSuccRightSucc m k) in
                                         Refl

reverseProof_nil : Vect n a -> Vect (plus n 0) a
reverseProof_nil {n} x = rewrite plusZeroRightNeutral n in x


reverseProof_xs : Vect ((S n) + k) a -> Vect (plus n (S k)) a
reverseProof_xs {n} {k} x = rewrite sym (plusSuccRightSucc n k) in x

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
      reverse' acc [] = reverseProof_nil acc
      reverse' acc (x :: xs) = reverseProof_xs (reverse' (x::acc) xs)
