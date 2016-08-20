-- ------------------------------------------------------------ [ Category.idr ]
-- Module    : Category.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
||| A logging resource that allows messages to be logged using both
||| numerical levels and user specified categories. The higher the
||| logging level the greater in verbosity the logging.
|||
||| The resource we are computing over is the logging level itself and
||| the list of categories to show.
module Resource.Logging.Category

import Resources
import public Resource.Logging.Levels

%access public export

-- -------------------------------------------------------- [ Logging Resource ]

||| The Logging details, this is the resource that the effect is
||| defined over.
record LogRes (a : Type) where
  constructor MkLogRes
  getLevel      : LogLevel n
  getCategories : List a

-- ------------------------------------------------------- [ Effect Definition ]

||| A Logging effect to log levels and categories.
data Logging : Resource_sig where
    ||| Log a message.
    |||
    ||| @lvl  The logging level it should appear at.
    ||| @cats The categories it should appear under.
    ||| @msg  The message to log.
    Log : (Show a, Eq a)
       => (lvl : LogLevel n)
       -> (cats : List a)
       -> (msg : String)
       -> Logging () (LogRes a) (const $ LogRes a)

    ||| Change the logging level.
    |||
    ||| @nlvl The new logging level
    SetLogLvl : (Show a, Eq a)
             => (nlvl : LogLevel n)
             -> Logging () (LogRes a) (const $ LogRes a)

    ||| Change the categories to show.
    |||
    ||| @ncats The new categories.
    SetLogCats : (Show a, Eq a)
              => (ncats : List a)
              -> Logging () (LogRes a) (const $ LogRes a)

    ||| Initialise the logging.
    |||
    ||| @nlvl  The new logging level.
    ||| @ncats The categories to show.
    InitLogging : (Show a, Eq a)
              => (nlvl  : LogLevel n)
              -> (ncats : List a)
              -> Logging () (LogRes a) (const $ LogRes a)

-- -------------------------------------------------------------- [ IO Handler ]

Execute Logging IO where
    exec res (SetLogLvl nlvl) k = do
        let newRes = record {getLevel = nlvl} res
        k () newRes
    exec res (SetLogCats newcs) k = do
        let newRes = record {getCategories = newcs} res
        k () newRes

    exec res  (InitLogging l cs) k = do
        let newRes = MkLogRes l cs
        k () newRes

    exec res (Log l cs' msg) k = do
      case cmpLevel l (getLevel res) of
        GT        => k () res
        otherwise =>  do
          let can_log = and $ map (\x => elem x cs') (getCategories res)
          let prompt = if isNil (getCategories res)
                         then unwords [show l, ":"]
                         else unwords [show l, ":", show (getCategories res), ":"]
          when (can_log || isNil (getCategories res)) $ do
              putStrLn $ unwords [prompt, msg]
          k () res

-- --------------------------------------------------------- [ Resourceful API ]

||| Change the logging level.
|||
||| @l  The new logging level.
setLoglvl : (Show a, Eq a)
         => (name : Var Logging)
         -> (l : LogLevel n)
         -> ResTrans m () ops [Stable name Logging (LogRes a)]
setLoglvl name l = on name $ SetLogLvl l

||| Change the categories to show.
|||
||| @cs The new categories.
setLogCats : (Show a, Eq a)
          => (name : Var Logging)
          -> (cs : List a)
          -> ResTrans m () ops [Stable name Logging (LogRes a)]
setLogCats name cs = on name $ SetLogCats cs

||| Initialise the Logging.
|||
||| @l  The logging level.
||| @cs The categories to show.
initLogging : (Show a, Eq a)
          => (name : Var Logging)
          -> (l    : LogLevel n)
          -> (cs   : List a)
          -> ResTrans m () ops [Stable name Logging (LogRes a)]
initLogging name l cs = on name $ InitLogging l cs

||| Log the given message at the given level indicated by a natural
||| number and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
log : (Show a, Eq a)
   => (name : Var Logging)
   -> (l    : LogLevel n)
   -> (cs   : List a)
   -> (msg  : String)
   -> ResTrans m () ops [Stable name Logging (LogRes a)]
log name l cs msg = on name $ Log l cs msg

||| Log the given message at the given level indicated by a natural number and assign it the list of categories.
|||
||| @l The logging level.
||| @cs The logging categories.
||| @m THe message to be logged.
logN : (Show a, Eq a)
    => (name : Var Logging)
    -> (l : Nat)
    -> {auto prf : LTE l 70}
    -> (cs : List a)
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging (LogRes a)]
logN name l cs msg = on name $ Log (snd lvl) cs msg
  where
    lvl : (n ** LogLevel n)
    lvl = case cast {to=String} (cast {to=Int} l) of
            "0"  => (_ ** OFF)
            "10" => (_ ** TRACE)
            "20" => (_ ** DEBUG)
            "30" => (_ ** INFO)
            "40" => (_ ** WARN)
            "50" => (_ ** FATAL)
            "60" => (_ ** ERROR)
            _    => (_ ** CUSTOM l)

trace : (Show a, Eq a)
     => (name : Var Logging)
     -> (cats : List a)
     -> (msg  : String )
     -> ResTrans m () ops [Stable name Logging (LogRes a)]
trace name cs msg = on name $ Log TRACE cs msg

debug : (Show a, Eq a)
     => (name : Var Logging)
     -> (cats : List a)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging (LogRes a)]
debug name cs msg = on name $ Log DEBUG cs msg

info : (Show a, Eq a)
    => (name : Var Logging)
    -> (cats : List a)
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging (LogRes a)]
info name cs msg = on name $ Log INFO cs msg

warn : (Show a, Eq a)
    => (name : Var Logging)
    -> (cats : List a)
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging (LogRes a)]
warn name cs msg = on name $ Log WARN cs msg

fatal : (Show a, Eq a)
     => (name : Var Logging)
     -> (cats : List a)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging (LogRes a)]
fatal name cs msg = on name $ Log FATAL cs msg

error : (Show a, Eq a)
     => (name : Var Logging)
     -> (cats : List a)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging (LogRes a)]
error name cs msg = on name $ Log ERROR cs msg

-- --------------------------------------------------------------------- [ EOF ]
