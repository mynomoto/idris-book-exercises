import System
import Data.Vect

printLength : IO ()
printLength = do putStr "Input string: "
                 input <- getLine
                 let len = length input
                 putStrLn (show len)

printLonger : IO ()
printLonger = do putStr "First string: "
                 input1 <- getLine
                 putStr "Second string: "
                 input2 <- getLine
                 let len1 = length input1
                 let len2 = length input2
                 if len1 > len2
                    then putStrLn (show len1)
                    else putStrLn (show len2)

printLength' : IO ()
printLength' = putStr "Input string: " >>= \_ =>
               getLine >>= \input =>
                           let len = length input in
                               putStrLn (show len)

printLonger' : IO ()
printLonger' = putStr "First string: " >>= \_ =>
               getLine >>= \input1 =>
               putStr "Second string: " >>= \_ =>
               getLine >>= \input2 =>
               let len1 = length input1
                   len2 = length input2 in
                   if len1 > len2
                      then putStrLn (show len1)
                      else putStrLn (show len2)

readNumber : IO (Maybe Nat)
readNumber = do input <- getLine
                if all isDigit (unpack input)
                  then pure (Just (cast input))
                  else pure Nothing

guess : (target : Nat) -> IO ()
guess target = do putStr "Guess a number: "
                  maybeNumber <- readNumber
                  (case maybeNumber of
                        Nothing => putStrLn "Not a number!"
                        (Just x) => (case compare x target of
                                          LT => do putStrLn "Too low!"
                                                   guess target
                                          EQ => putStrLn "Correct!"
                                          GT => do putStrLn "Too high!"
                                                   guess target))

main : IO ()
main = do secs <- time
          let randomNumber = (mod secs 100) + 1
          guess (cast randomNumber)

guess' : (target : Nat) -> (guesses : Nat) -> IO ()
guess' target guesses = do let msg = "Guess a number (" ++ (show guesses) ++ " attempts): "
                           putStr msg
                           maybeNumber <- readNumber
                           case maybeNumber of
                                Nothing => putStrLn "Not a number!"
                                (Just x) => (case compare x target of
                                                  LT => do putStrLn "Too low!"
                                                           guess' target (S guesses)
                                                  EQ => putStrLn "Correct!"
                                                  GT => do putStrLn "Too high!"
                                                           guess' target (S guesses))

repl' : String -> (String -> String) -> IO ()
repl' prompt f = do putStr prompt
                    line <- getLine
                    putStr (f line)
                    repl' prompt f

replWith' : (state : a) -> (prompt : String) -> (onInput : a -> String -> Maybe (String, a)) -> IO ()
replWith' state prompt onInput = do putStr prompt
                                    line <- getLine
                                    (case (onInput state line) of
                                          Nothing => pure ()
                                          (Just (response, new_state)) => do putStr response
                                                                             replWith' new_state prompt onInput)

readToBlank : IO (List String)
readToBlank = do line <- getLine
                 if (line == "")
                    then pure []
                    else do l <- readToBlank
                            pure (line :: l)

readAndSave : IO ()
readAndSave = do lines <- readToBlank
                 putStr "Filename: "
                 filename <- getLine
                 do Right () <- writeFile filename (unlines lines) | Left err => putStrLn ("Error " ++ (show err))
                    putStrLn "File written"

readLines : File -> IO (n ** Vect n String)
readLines file = do Right line <- fGetLine file | Left err => do putStrLn (show err)
                                                                 pure (_ ** [])
                    eof <- fEOF file
                    if eof
                       then do closeFile file
                               pure (_ ** [])
                       else do (_ ** moreLines) <- readLines file
                               pure (_ ** (line :: moreLines))

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do Right file <- openFile filename Read | Left err => do putStrLn (show err)
                                                                                 pure (_ ** [])
                           readLines file
