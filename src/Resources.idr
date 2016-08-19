module Resources

import public Data.List
import public Utils.SubList

%default total

public export
Resource_sig : Type
Resource_sig = (ty : Type) -> Type -> (ty -> Type) -> Type

public export
data Resource : Type where
     MkRes : label -> Resource_sig -> ty -> Resource

export
data Var : Resource_sig -> Type where
     MkVar : Var r

public export
interface Execute (r : Resource_sig) (m : Type -> Type) where
     covering
     exec : inr -> r ty inr outfn -> 
            (k : (x : ty) -> outfn x -> m a) -> m a

-- This needs to be a specialised type, rather than a generic List,
-- because resources might contain List as a type, and we'd end up with
-- a universe cycle.
public export
data Context : Type where
     Nil : Context
     (::) : Resource -> Context -> Context

namespace Env
  public export
  data Env : (m : Type -> Type) -> Context -> Type where
       Nil : Env m Nil
       (::) : Execute res m => a -> Env m xs -> Env m (MkRes lbl res a :: xs)

namespace Execs
  public export
  data Execs : (m : Type -> Type) -> List Resource_sig -> Type where
       Nil : Execs m Nil
       (::) : Execute res m -> Execs m xs -> Execs m (res :: xs)

  getExecute : Execs m rs -> Elem iface rs -> Execute iface m
  getExecute (h :: xs) Here = h
  getExecute (x :: xs) (There later) = getExecute xs later

public export
(++) : Context -> Context -> Context
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

public export
appendNilRightNeutral : (l : Context) -> l ++ [] = l
appendNilRightNeutral [] = Refl
appendNilRightNeutral (x :: xs) = cong (appendNilRightNeutral xs)

-- --------------------------------------- [ Properties and Proof Construction ]

public export
data HasIFace : Type -> (r : Resource_sig) -> Var r -> Context -> Type where
     Here : HasIFace ty iface lbl (MkRes lbl iface ty :: rs)
     There : HasIFace ty iface lbl rs -> HasIFace ty iface lbl (r :: rs)

public export
data ElemCtxt : a -> Context -> Type where
  HereCtxt : ElemCtxt a (a :: as)
  ThereCtxt : ElemCtxt a as -> ElemCtxt a (b :: as)

public export
data SubCtxt : Context -> Context -> Type where
  SubNil : SubCtxt [] xs
  InCtxt : ElemCtxt x ys -> SubCtxt xs ys -> SubCtxt (x :: xs) ys

Uninhabited (ElemCtxt x []) where
  uninhabited HereCtxt impossible
  uninhabited (ThereCtxt _) impossible

-- Some useful hints for proof construction in polymorphic programs
%hint
public export total
dropFirst : SubCtxt xs ys -> SubCtxt xs (x :: ys)
dropFirst SubNil = SubNil
dropFirst (InCtxt el sub) = InCtxt (ThereCtxt el) (dropFirst sub)

%hint
public export total
subListId : (xs : Context) -> SubCtxt xs xs
subListId [] = SubNil
subListId (x :: xs) = InCtxt HereCtxt (dropFirst (subListId xs))

public export total
inSuffix : ElemCtxt x ys -> SubCtxt xs ys -> ElemCtxt x (zs ++ ys)
inSuffix {zs = []} el sub = el
inSuffix {zs = (x :: xs)} el sub = ThereCtxt (inSuffix el sub)

%hint
public export total
dropPrefix : SubCtxt xs ys -> SubCtxt xs (zs ++ ys)
dropPrefix SubNil = SubNil
dropPrefix (InCtxt el sub) = InCtxt (inSuffix el sub) (dropPrefix sub)

public export total
inPrefix : ElemCtxt x ys -> SubCtxt xs ys -> ElemCtxt x (ys ++ zs)
inPrefix {zs = []} {ys} el sub
    = rewrite appendNilRightNeutral ys in el
inPrefix {zs = (x :: xs)} HereCtxt sub = HereCtxt
inPrefix {zs = (x :: xs)} (ThereCtxt y) sub = ThereCtxt (inPrefix y SubNil)

%hint
public export total
dropSuffix : SubCtxt xs ys -> SubCtxt xs (ys ++ zs)
dropSuffix SubNil = SubNil
dropSuffix (InCtxt el sub) = InCtxt (inPrefix el sub) (dropSuffix sub)

public export
total updateAt : (idx : ElemCtxt x' xs) -> (a : ty) -> Context -> Context
updateAt HereCtxt a [] = []
updateAt HereCtxt a (MkRes lbl eff b :: xs) = MkRes lbl eff a :: xs
updateAt (ThereCtxt k) a [] = []
updateAt (ThereCtxt k) a (x :: xs) = x :: updateAt k a xs

public export
total updateWith : (ys' : Context) -> (xs : Context) ->
             SubCtxt ys xs -> Context
updateWith [] xs sl = xs
updateWith (y :: ys) xs SubNil = xs
updateWith (MkRes lbl f a :: ys) xs (InCtxt idx rest) = updateAt idx a (updateWith ys xs rest)

envElem : ElemCtxt x xs -> Env m xs -> Env m [x]
envElem HereCtxt (x :: xs) = [x]
envElem (ThereCtxt later) (x :: xs) = envElem later xs

total
dropEnv : Env m ys -> SubCtxt xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv [] (InCtxt idx rest) = absurd idx
dropEnv (y :: ys) SubNil = []
dropEnv e@(y :: ys) (InCtxt idx rest) 
    = let [x] = envElem idx e in
          x :: dropEnv e rest

execsElem : Elem x xs -> Execs m xs -> Execs m [x]
execsElem Here (x :: xs) = [x]
execsElem (There later) (x :: xs) = execsElem later xs

total
dropExecs : Execs m ys -> SubList xs ys -> Execs m xs
dropExecs [] SubNil = []
dropExecs [] (InList idx rest) = absurd idx
dropExecs (y :: ys) SubNil = []
dropExecs e@(y :: ys) (InList idx rest) 
     = let [x] = execsElem idx e in
           x :: dropExecs e rest

replaceEnvAt : (x : a) -> (idx : ElemCtxt x' xs) -> Env m ys ->
               Env m (updateAt idx a ys)
replaceEnvAt x HereCtxt [] = []
replaceEnvAt x HereCtxt (y :: ys) = x :: ys
replaceEnvAt x (ThereCtxt p) [] = []
replaceEnvAt x (ThereCtxt p) (y :: ys) = y :: replaceEnvAt x p ys

total
rebuildEnv : {ys' : Context} ->
             Env m ys' -> (prf : SubCtxt ys xs) ->
             Env m xs -> Env m (updateWith ys' xs prf)
rebuildEnv [] SubNil env = env
rebuildEnv (x :: xs) SubNil env = env
rebuildEnv [] (InCtxt idx rest) env = env
rebuildEnv (x :: xs) (InCtxt idx rest) env 
      = replaceEnvAt x idx (rebuildEnv xs rest env)

public export
drop : (ctxt : Context) -> HasIFace ty iface lbl ctxt -> Context
drop ((MkRes lbl iface ty1) :: rs) Here = rs
drop (r :: rs) (There x) = r :: drop rs x

dropVal : (prf : HasIFace ty iface lbl ctxt) -> Env m ctxt -> Env m (drop ctxt prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

public export
updateCtxt : (ctxt : Context) -> HasIFace ty iface lbl ctxt -> Type -> Context
updateCtxt ((MkRes lbl iface _) :: rs) Here ty 
      = ((MkRes lbl iface ty) :: rs)
updateCtxt (r :: rs) (There x) ty = r :: updateCtxt rs x ty

export
data Res : (m : Type -> Type) ->
           (ty : Type) -> 
           List Resource_sig ->
           Context -> (ty -> Context) -> Type where

     Pure : (x : val) -> Res m val ops (ctxtk x) ctxtk
     Bind : Res m a ops rs rs' -> 
            ((x : a) -> Res m b ops (rs' x) rs'') ->
            Res m b ops rs rs''

     New : (iface : Resource_sig) ->
           {auto prf : Elem iface ops} ->
           ty ->
           Res m (Var iface) ops ctxt (\lbl => MkRes lbl iface ty :: ctxt)
     Delete : (lbl : Var iface) -> {auto prf : HasIFace ty iface lbl ctxt} ->
              Res m () ops ctxt (const (drop ctxt prf))

     On : (lbl : Var iface) ->
          {auto prf : HasIFace in_state iface lbl ctxt} ->
          (op : iface t in_state out_fn) ->
          Res m t ops ctxt (\result => updateCtxt ctxt prf (out_fn result))

     Call : {auto op_prf : SubList ops' ops} ->
            Res m t ops' ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            Res m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)
     Lift : Monad m => m t -> Res m t ops ctxt (const ctxt)

export
(>>=) : Res m a ops rs rs' -> 
        ((x : a) -> Res m b ops (rs' x) rs'') ->
        Res m b ops rs rs''
(>>=) prog next = Bind prog (\res => next res)


export
pure : (x : val) -> Res m val ops (ctxtk x) ctxtk
pure = Pure

export
new : (iface : Resource_sig) ->
      {auto prf : Elem iface ops} ->
      ty ->
      Res m (Var iface) ops ctxt (\lbl => MkRes lbl iface ty :: ctxt)
new = New

export
delete : (lbl : Var iface) -> {auto prf : HasIFace ty iface lbl ctxt} ->
         Res m () ops ctxt (const (drop ctxt prf))
delete = Delete

export
on : (lbl : Var iface) ->
     {auto prf : HasIFace in_state iface lbl ctxt} ->
     (op : iface t in_state out_fn) ->
     Res m t ops ctxt (\result => updateCtxt ctxt prf (out_fn result))
on = On

export
call : {auto op_prf : SubList ops' ops} ->
       Res m t ops' ys ys' ->
       {auto ctxt_prf : SubCtxt ys xs} ->
       Res m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)
call = Call

export
lift : Monad m => m t -> Res m t ops ctxt (const ctxt)
lift = Lift

namespace Loop
  public export
  data ResLoop : (m : Type -> Type) -> (ty : Type) -> 
                 List Resource_sig -> Context -> Type where
       Do : Res m a ops inr outfn -> 
            ((val : a) -> Inf (ResLoop m b ops (outfn val))) ->
            ResLoop m b ops inr 
       Call : ResLoop m b ops_sub inr ->
              {auto prf : SubList ops_sub ops} -> 
              ResLoop m b ops inr
       Exit : ty -> ResLoop m ty ops inr

  public export 
  (>>=) : Res m a ops inr outfn -> 
          ((val : a) -> Inf (ResLoop m b ops (outfn val))) ->
          ResLoop m b ops inr 
  (>>=) = Do

  export
  exit : ty -> ResLoop m ty ops inr
  exit = Exit
      
  export
  call : ResLoop m b ops_sub inr ->
         {auto prf : SubList ops_sub ops} ->
         ResLoop m b ops inr
  call = Call

public export
data Action : Type -> Type where
     Stable : label -> Resource_sig -> Type -> Action ty
     Trans : label -> Resource_sig -> Type -> (ty -> Type) -> Action ty

public export
ResTrans : (m : Type -> Type) ->
           (ty : Type) -> 
           (ops : List Resource_sig) ->
           List (Action ty) -> Type
ResTrans m ty ops xs = Res m ty ops (in_res xs) (\x : ty => out_res x xs)
  where
    out_res : ty -> List (Action ty) -> Context
    out_res x [] = []
    out_res x (Stable lbl sig inr :: xs) = MkRes lbl sig inr :: out_res x xs
    out_res x (Trans lbl sig inr outr :: xs) 
                                    = MkRes lbl sig (outr x) :: out_res x xs

    in_res : List (Action ty) -> Context
    in_res [] = []
    in_res (Stable lbl sig inr :: xs) = MkRes lbl sig inr :: in_res xs
    in_res (Trans lbl sig inr outr :: xs) = MkRes lbl sig inr :: in_res xs

public export
ResOp : (m : Type -> Type) -> Type -> Type
ResOp m ty = {ops : _} -> {ctxt : _} -> Res m ty ops ctxt (const ctxt)

private 
execRes : Env m ctxt -> 
          (prf : HasIFace in_state iface lbl ctxt) ->
          (op : iface t in_state out_fn) ->
          ((x : t) -> Env m (updateCtxt ctxt prf (out_fn x)) -> m b) ->
          m b
execRes (val :: env) Here op k
        = exec val op (\v, res => k v (res :: env))
execRes (val :: env) (There p) op k 
        = execRes env p op (\v, env' => k v (val :: env'))

export 
runRes : Env m inr -> Execs m ops ->
         Res m a ops inr outfn ->
         ((x : a) -> Env m (outfn x) -> m b) -> m b
runRes env execs (Pure x) k = k x env
runRes env execs (Bind prog next) k 
  = runRes env execs prog (\prog', env' => runRes env' execs (next prog') k)
runRes env execs (New {prf} iface val) k 
  = let h = getExecute execs prf in
        k MkVar (val :: env)
runRes env execs (Delete {prf} name) k 
  = k () (dropVal prf env)
runRes env execs (On {prf} name op) k 
  = execRes env prf op k
runRes env execs (Call {op_prf} prog {ctxt_prf}) k 
  = let env' = dropEnv env ctxt_prf
        execs' = dropExecs execs op_prf in
        runRes env' execs' prog 
               (\prog', envk => k prog' (rebuildEnv envk ctxt_prf env))
runRes env execs (Lift action) k 
  = do res <- action
       k res env

export
data Fuel = Empty | More (Lazy Fuel)

export
partial forever : Fuel
forever = More forever

export
steps : Nat -> Fuel
steps Z = Empty
steps (S k) = More (steps k)

loopRes : Applicative m =>
          Fuel -> Env m inr -> Execs m ops ->
          ResLoop m a ops inr -> m (Maybe a)
loopRes (More x) env execs (Do act k) 
  = runRes env execs act (\res, env' => loopRes x env' execs (k res))
loopRes (More x) env execs (Call prog {prf}) 
  = let execs' = dropExecs execs prf in
        loopRes x env execs' prog
loopRes x env execs (Exit res) = pure (Just res)
loopRes Empty _ _ _ = pure Nothing

export total
run : Applicative m => 
      {auto execs : Execs m ops} -> Res m a ops [] (const []) -> 
      m a
run {execs} prog = runRes [] execs prog (\res, env' => pure res)

export total
eval : {auto execs : Execs Basics.id ops} ->  
       Res Basics.id a ops [] (const []) ->
       a
eval {execs} prog = runRes [] execs prog (\res, env' => res)

export total
loop : Applicative m =>
       Fuel ->
       {auto execs : Execs m ops} -> ResLoop m a ops [] ->
       m (Maybe a)
loop fuel {execs} prog = loopRes fuel [] execs prog
