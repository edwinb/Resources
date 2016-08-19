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
         ResTrans m () 
                  ops -- Things we're allowed to create
                  [Trans name State a (const b)] -- How we update and use resources
update name f = do val <- On name Get
                   On name (Put (f val))

export
get : (name : Var State) -> ResTrans m ty ops [Stable name State ty]
get name = On name Get

export
put : (name : Var State) -> b -> ResTrans m () ops [Trans name State a (const b)]
put name val = On name (Put val)

infix 5 :=

export
(:=) : (name : Var State) -> b -> ResTrans m () ops [Trans name State a (const b)]
(:=) = put 

