-- ------------------------------------------------------------- [ Default.idr ]
-- Module    : Default.idr
-- Copyright : (c) The Idris Community
-- License   : see LICENSE
--------------------------------------------------------------------- [ EOH ]
||| The default logging effect that allows messages to be logged at
||| different numerical levels. The higher the number the greater in
||| verbosity the logging.
|||
||| In this effect the resource we are computing over is the logging
||| level itself.
|||
module Resource.Logging.Default

import Resources
import public Resource.Logging.Levels

%access public export

-- ------------------------------------------------------------ [ The Resource ]

||| The resource.
record LogRes where
  constructor MkLogRes
  getLevel : LogLevel n

||| A Logging Resource that displays a logging message to be logged at
||| a certain level.
data Logging : Resource_sig where
    ||| Change the logging level.
    |||
    ||| @lvl The new logging level.
    SetLvl : (lvl : LogLevel n)
          -> Logging () (LogRes) (const LogRes)

    ||| Log a message.
    |||
    ||| @lvl  The logging level it should appear at.
    ||| @msg  The message to log.
    Log : (lvl : LogLevel n)
       -> (msg : String)
       -> Logging () (LogRes) (const LogRes)

-- --------------------------------------------------------- [ Implementations ]

-- For logging in the IO context
Execute Logging IO where
    exec _   (SetLvl newLvl) k = k () (MkLogRes newLvl)
    exec res (Log lvl msg)   k = do
      case cmpLevel lvl (getLevel res)  of
        GT        => k () res
        otherwise =>  do
          putStrLn $ unwords [show lvl, ":", msg]
          k () res

-- --------------------------------------------------------- [ Resourceful API ]

||| Set the logging level.
|||
||| @l The new logging level.
setLogLvl : (name : Var Logging)
         -> (l : LogLevel n)
         -> ResTrans m () ops [Stable name Logging LogRes]
setLogLvl name l = on name (SetLvl l)

||| Log `msg` at the given level specified as a natural number.
|||
||| @l The level to log.
||| @m The message to log.
log : (name : Var Logging)
   -> (l : LogLevel n)
   -> (msg : String)
   -> ResTrans m () ops [Stable name Logging LogRes]
log name l msg = on name $ Log l msg

||| Log `msg` at the given level specified as a natural number.
|||
||| @l The level to log.
||| @m The message to log.
logN : (name : Var Logging)
    -> (l : Nat)
    -> {auto prf : LTE l 70}
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging LogRes]
logN name l msg = on name $ Log (snd lvl) msg
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

trace : (name : Var Logging)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging LogRes]
trace name msg = on name $ Log TRACE msg

debug : (name : Var Logging)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging LogRes]
debug name msg = on name $ Log DEBUG msg

info : (name : Var Logging)
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging LogRes]
info name msg = on name $ Log INFO msg

warn : (name : Var Logging)
    -> (msg : String)
    -> ResTrans m () ops [Stable name Logging LogRes]
warn name msg = on name $ Log WARN msg

fatal : (name : Var Logging)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging LogRes]
fatal name msg = on name $ Log FATAL msg

error : (name : Var Logging)
     -> (msg : String)
     -> ResTrans m () ops [Stable name Logging LogRes]
error name msg = on name $ Log ERROR msg

-- --------------------------------------------------------------------- [ EOF ]
