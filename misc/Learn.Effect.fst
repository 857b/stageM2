module Learn.Effect

type req_t = nat -> prop
type ens_t (req : req_t) (a : Type) = (s0 : nat {req s0}) -> a -> nat -> prop

type repr (a : Type) (req : req_t) (ens : ens_t req a) =
  s0:nat -> Pure (a & nat)
            (requires req s0)
            (ensures  fun (res, s1) -> ens s0 res s1)


unfold
let return_req : req_t
  = fun (_:nat) -> True

unfold
let return_ens (a : Type) (x : a) : ens_t (return_req) a
  = fun (s0 : nat) (r : a) s1 -> r == x /\ s1 == s0

let return (a : Type) (x : a) : repr a return_req (return_ens a x)
  = fun (s0 : nat) -> (x, s0)


unfold
let bind_req (#a : Type)
      (req_f : req_t)     (ens_f : ens_t req_f a)
      (req_g : a -> req_t)
  : req_t
  = fun (s0 : nat) -> req_f s0 /\ (forall (x : a) (s1 : nat) . ens_f s0 x s1 ==> req_g x s1)

unfold
let bind_ens (#a : Type) (#b : Type)
      (req_f : req_t)     (ens_f : ens_t req_f a)
      (req_g : a -> req_t) (ens_g : (x:a) -> ens_t (req_g x) b)
  : ens_t (bind_req req_f ens_f req_g) b
  = fun (s0 : nat {req_f s0}) (y : b) (s2 : nat) ->
      exists (x : a) (s1 : nat {req_g x s1}) .
        ens_f s0 x s1 /\ ens_g x s1 y s2

let bind (a : Type) (b : Type)
      (#req_f : req_t)     (#ens_f : ens_t req_f a)
      (#req_g : a -> req_t) (#ens_g : (x:a) -> ens_t (req_g x) b)
      (f : repr a req_f ens_f) (g : (x:a) -> repr b (req_g x) (ens_g x))
  : repr b (bind_req req_f ens_f req_g) (bind_ens req_f ens_f req_g ens_g)
  = fun (s0 : nat) ->
      let (x, s1) = f s0 in
      g x s1


unfold
let subcomp_pre (#a : Type)
      (req_f : req_t) (ens_f : ens_t req_f a)
      (req_g : req_t) (ens_g : ens_t req_g a)
  : pure_pre
  = forall (s0 : nat) . req_g s0 ==> (req_f s0 /\
      (forall (x : a) (s1 : nat) . ens_f s0 x s1 ==> ens_g s0 x s1))

let subcomp (a : Type)
      (req_f : req_t) (ens_f : ens_t req_f a)
      (req_g : req_t) (ens_g : ens_t req_g a)
      (f : repr a req_f ens_f)
  : Pure (repr a req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
         (ensures fun _ -> True)
  = f


unfold
let if_then_else_req
      (req_then : req_t) (req_else : req_t)
      (p : Type0)
  : req_t
  = fun s0 -> (p  ==> req_then s0) /\
           (~p ==> req_else s0)

unfold
let if_then_else_ens (#a : Type)
      (req_then : req_t) (ens_then : ens_t req_then a)
      (req_else : req_t) (ens_else : ens_t req_else a)
      (p : Type0)
  : ens_t (if_then_else_req req_then req_else p) a
  = fun (s0 : nat {if_then_else_req req_then req_else p s0}) (x : a) (s1 : nat) ->
      (p  ==> ens_then s0 x s1) /\
      (~p ==> ens_else s0 x s1)

let if_then_else (a : Type)
      (#req_then : req_t) (#ens_then : ens_t req_then a)
      (#req_else : req_t) (#ens_else : ens_t req_else a)
      (f : repr a req_then ens_then)
      (g : repr a req_else ens_else)
      (p : bool)
  = repr a (if_then_else_req req_then req_else p)
           (if_then_else_ens req_then ens_then req_else ens_else p)

reflectable
effect {
  NState (a : Type) (req : req_t) (ens : ens_t req a)
  with {
    repr;
    return;
    bind;
    subcomp;
    if_then_else
  }
}


unfold
let bind_pure_nstate_req (#a : Type) (wp : pure_wp a)
      (req : a -> req_t)
  : req_t
  = fun s0 -> squash (wp (fun x -> req x s0))

unfold
let bind_pure_nstate_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (req : a -> req_t) (ens : (x : a) -> ens_t (req x) b)
  : ens_t (bind_pure_nstate_req wp req) b
  = fun s0 y s1 -> as_requires wp /\
      (exists (x : a) . as_ensures wp x /\ (FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp; ens x s0 y s1))

let bind_pure_nstate (a : Type) (b : Type)
      (#wp : pure_wp a)
      (req : a -> req_t) (ens : (x : a) -> ens_t (req x) b)
      (f : eqtype_as_type unit -> PURE a wp) (g : (x : a) -> repr b (req x) (ens x))
  : repr b (bind_pure_nstate_req wp req) (bind_pure_nstate_ens wp req ens)
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun s0 ->
      let x = f () in
      g x s0

#push-options "--warn_error -330"  //turn off the experimental feature warning
polymonadic_bind (PURE, NState) |> NState = bind_pure_nstate
#pop-options


let read () : NState nat (requires fun _ -> True) (ensures fun s0 x s1 -> s1 = s0 /\ x = s0)
  = NState?.reflect (fun s0 -> s0,s0)

let write (x : nat) : NState unit (requires fun _ -> True) (ensures fun s0 () s1 -> s1 == x)
  = NState?.reflect (fun _ -> (),x)

let incr () : NState unit (requires fun _ -> True) (ensures fun s0 () s1 -> s1 == s0 + 1)
  = let x = read () in
    write (x + 1)
