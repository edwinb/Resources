import Data.Vect
import States


data ValOp : State_sig Type where
     Get : ValOp a a (const a)
     Put : b -> ValOp () a (const b)

Val : Type -> SM Type
Val a = MkSM a (const ()) (\x => x) ValOp

Execute (Val ty) m where
    exec res Get     k = k res res
    exec res (Put x) k = k () x

data HangmanState = Unstarted | Playing | Won | Lost

data GameEnd : HangmanState -> Type where
     GameWon : GameEnd Won
     GameLost : GameEnd Lost

data HangmanOp : State_sig HangmanState where
     NewGame : (word : String) -> HangmanOp () Unstarted (const Playing)
     Play : HangmanOp Bool Playing (\res => case res of
                                                 True => Won
                                                 False => Lost)

data HangmanData : HangmanState -> Type where
     Word : String -> HangmanData Playing
     NoWord : HangmanData x

Hangman : SM HangmanState
Hangman = MkSM Unstarted GameEnd HangmanData HangmanOp

hangman : StateTrans IO () [Hangman] []
hangman = do game <- New Hangman NoWord
             On game $ NewGame "testing"
             result <- On game Play
             case result of
                  False => do Lift (putStrLn "You lose")
                              Delete game
                  True => do Lift (putStrLn "You win")
                             Delete game

data GameState = Score Nat Nat
               | NotRunning

data Finished : GameState -> Type where
     GameFinished : Finished NotRunning

letters : String -> List Char
letters str = map toUpper (nub (unpack str))

data GameOp : State_sig GameState where
     Guess : Char -> GameOp Bool (Score (S g) (S l))
                            (\res => case res of
                                          False => Score g (S l)
                                          True => Score (S g) l)
     ReadGuess : GameOp Char (Score (S g) (S l)) (const (Score (S g) (S l)))

     ClaimWin  : GameOp () (Score (S g) 0) (const NotRunning)
     AdmitLoss : GameOp () (Score 0 (S l)) (const NotRunning)
     GetState  : GameOp String st (const st)
     SetTarget : (word : String) -> GameOp () NotRunning 
                                      (const (Score 6 (length (letters word))))

data GameData : GameState -> Type where
     InProgress : (target : String) -> (g : Nat) ->
                  (missing : Vect l Char) -> 
                  GameData (Score g l)
     MkNotRunning : (won : Bool) -> GameData NotRunning

Show (GameData g) where
    show (MkNotRunning won) = if won then "Game won" else "Game lost"
    show (InProgress word guesses missing) 
         = "\n" ++ pack (map hideMissing (unpack word)) 
               ++ "\n" ++ show guesses ++ " guesses left"
      where hideMissing : Char -> Char
            hideMissing c = if c `elem` missing then '-' else c 

Game : SM GameState
Game = MkSM NotRunning Finished GameData GameOp

play : (game : Var Game) ->
       StateTrans IO Bool [] [Trans game Game (Score (S g) l)
                                              (const NotRunning)]
play {g} {l = Z} game = do On game ClaimWin
                           Pure True
play {g} {l = S l} game 
      = do st <- On game GetState
           Lift (putStrLn st)
           letter <- On game ReadGuess
           ok <- On game (Guess letter)
           case ok of
                False => do Lift (putStrLn "Incorrect")
                            case g of
                                 Z => do On game AdmitLoss
                                         Pure False
                                 S k => play game
                True => do Lift (putStrLn "Correct!")
                           play game

Transform HangmanState Type Hangman (Val String) [Game] IO where

    toState x = String
    toResource Playing (Word x) = x
    toResource st NoWord = ""

    fromResource Unstarted res = NoWord
    fromResource Playing res = Word res
    fromResource Won res = NoWord
    fromResource Lost res = NoWord

    transform word (NewGame x) = On word (Put x)
    transform word Play = do x <- On word Get
                             game <- New Game (MkNotRunning False)
                             On game (SetTarget (toUpper x))
                             result <- Call (play game)
                             Delete game
                             case result of
                                  True => Pure True
                                  False => Pure False

total
removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later}
                                          = y :: removeElem value ys

Execute Game IO where
    exec (InProgress word _ missing) (Guess x) k = 
         case isElem x missing of
              Yes prf => k True (InProgress word _ (removeElem x missing))
              No contra => k False (InProgress word _ missing)
    exec res ReadGuess k = do putStr "Guess: "
                              x <- getLine
                              case unpack (toUpper x) of
                                   [letter] => if isAlpha letter
                                                  then k letter res
                                                  else k ' ' res
                                   _ => k ' ' res
    exec res ClaimWin k = k () (MkNotRunning True)
    exec res AdmitLoss k = k () (MkNotRunning False)
    exec res GetState k = k (show res) res
    exec res (SetTarget word) k = k () (InProgress word _ (fromList (letters word)))

