module Interface.IO

import Resources

public export
interface Monad m => ConsoleIO (m : Type -> Type) where
  putStr : String -> ResOp m () 
  getStr : ResOp m String

export
ConsoleIO IO where
  putStr str = Lift (Interactive.putStr str)
  getStr = Lift getLine

using (ConsoleIO io)
  export
  putStrLn : String -> ResOp io ()
  putStrLn str = putStr (str ++ "\n")

  export
  print : Show a => a -> ResOp io ()
  print x = putStr (show x)

  export
  printLn : Show a => a -> ResOp io ()
  printLn x = putStrLn (show x)

