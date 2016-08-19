module Interface.IO

import Resources
import Control.IOExcept

%default total

public export
interface ConsoleIO (m : Type -> Type) where
  putStr : String -> ResOp m () 
  getStr : ResOp m String

export
ConsoleIO IO where
  putStr str = lift (putStr str)
  getStr = lift getLine

ConsoleIO (IOExcept err) where 
  putStr str = lift (ioe_lift (putStr str))
  getStr = lift (ioe_lift getLine)

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

