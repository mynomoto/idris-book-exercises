data SnocListNR ty = EmptyNR
                   | SnocNR (SnocListNR ty) ty

reverseSnoc : SnocListNR ty -> List ty
reverseSnoc EmptyNR = []
reverseSnoc (SnocNR xs x) = x :: reverseSnoc xs

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocList : (xs : List a) -> SnocList xs
