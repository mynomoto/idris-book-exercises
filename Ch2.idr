palindrome : String -> Bool
palindrome x = x == reverse x

palindrome_ci : String -> Bool
palindrome_ci x = (toLower x) == reverse (toLower x)

palindrome_big : String -> Bool
palindrome_big x = if length x > 10
                      then palindrome x
                      else False

palindrome_size : Nat -> String -> Bool
palindrome_size k x = if length x > k
                         then palindrome x
                         else False

counts : String -> (Nat, Nat)
counts x = (length (words x),length x)

top_ten : Ord a => List a -> List a
top_ten xs = take 10 (reverse (sort xs))

over_length : Nat -> List String -> Nat
over_length k xs = length (filter (\w => (length w) > k) xs)

palindrome_repl : IO ()
palindrome_repl = repl "Enter a string: " ((++ "\n") . show . palindrome)

allLengths : List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs
