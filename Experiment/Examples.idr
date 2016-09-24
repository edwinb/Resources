import States

data DoorState = Open | Closed

data DoorFinal : DoorState -> Type where
     MustBeClosed : DoorFinal Closed

data DoorOp : State_sig DoorState where
     RingBell : DoorOp () Closed (const Closed)
     OpenDoor : DoorOp () Closed (const Open)
     CloseDoor : DoorOp () Open (const Closed)

Door : SM DoorState
Door = MkSM Closed DoorFinal (const ()) DoorOp

doorProg : States m () [Door] [] (const [])
doorProg = do d <- New Door ()
              On d RingBell
              On d OpenDoor
              On d CloseDoor
              Delete d

data ValOp : State_sig Type where
     Get : ValOp a a (const a)
     Put : b -> ValOp () a (const b)

Val : Type -> SM Type
Val a = MkSM a (const ()) (\x => x) ValOp

Execute (Val ty) m where
    exec res Get     k = k res res
    exec res (Put x) k = k () x

valProg : States m () [Val Integer] [] (const [])
valProg = do num <- New (Val _) 42
             val <- On num Get
             On num (Put (val + 1))
             Delete num

Transform DoorState Type Door (Val Bool) [Val Int] IO where
    toState Open = Bool
    toState Closed = Bool

    toResource Open = True
    toResource Closed = False

    fromResource ops res = ()

    transform door RingBell = Lift (putStrLn "Bing bong")

    transform door OpenDoor = do Lift (putStrLn "Opening")
                                 silly <- New (Val Int) 20
                                 On door (Put True)
                                 Delete silly
    transform door CloseDoor = do Lift (putStrLn "Closing")
                                  On door (Put False)

main : IO ()
main = run doorProg

