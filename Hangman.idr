import Data.Vect

-- %default total

data WordState : (guessesRemaning : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) -> (missing : Vect letters Char) -> WordState guessesRemaning letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won : (game: WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]

isEmpty : ValidInput [] -> Void
isEmpty (Letter _) impossible

manyChars : ValidInput (x :: (y :: xs)) -> Void
manyChars (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No isEmpty
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No manyChars

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess: "
               input <- getLine
               case isValidString (toUpper input) of
                    (Yes prf) => pure (_ ** prf)
                    (No contra) => do putStrLn "Invalid guess"
                                      readGuess

processGuess : (letter : Char) -> WordState (S guesses) (S letters) -> Either (WordState guesses (S letters))
                                                                              (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = ?processGuess_rhs_1

game : WordState (S guesses) (S letters) -> IO Finished
game x = ?game_rhs

main : IO ()
main = do x <- readGuess
          pure ()
