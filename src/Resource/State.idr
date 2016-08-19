module Resource.State

import Resources

public export
data State : Resource_sig where
     Get : State ty ty (const ty)
     Put : (val : ty) -> State () old (const ty)

export
Execute State m where
    exec st Get k = k st st
    exec st (Put val) k = k () val

export
update : (name : Var State) -> (a -> b) ->
         ResTrans m () ops [Trans name State a (const b)] 
update name f = do val <- on name Get
                   on name (Put (f val))

export
get : (name : Var State) -> ResTrans m ty ops [Stable name State ty]
get name = on name Get

export
put : (name : Var State) -> b -> ResTrans m () ops [Trans name State a (const b)]
put name val = on name (Put val)

infix 5 :=

export
(:=) : (name : Var State) -> b -> ResTrans m () ops [Trans name State a (const b)]
(:=) = put 

