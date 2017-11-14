import Data.Vect
import RemoveElem

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
processGuess letter (MkWordState word missing) = case isElem letter missing of
                                                      (Yes prf) => Right (MkWordState word (removeElem letter missing))
                                                      (No contra) => Left (MkWordState word missing)

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} state =
     do (_ ** Letter letter) <- readGuess
        case processGuess letter state of
             Left l => do putStrLn "Wrong!"
                          case guesses of
                               Z => pure (Lost l)
                               (S k) => game l
             Right r => do putStrLn "Correct!"
                           case letters of
                                Z => pure (Won r)
                                (S k) => game r

main : IO ()
main = do result <- game {guesses = 2} (MkWordState "Test" ['T', 'E', 'S'])
          (case result of
                (Lost (MkWordState word missing)) => putStrLn ("You lose. The word was " ++ word)
                (Won (MkWordState word missing)) => putStrLn ("You win. The word was " ++ word))
