module Learn.Effect.NonDeterminism


type req_t = prop
type ens_t (a : Type) (req : req_t) = a -> Pure prop (requires req) (ensures fun _ -> True)

type repr (a : Type) (req : req_t) (ens : ens_t a req) =
  (x:a) -> Pure prop (requires req) (ensures fun p -> p ==> ens x)

(** return *)

unfold
let return_req : req_t
  = True

unfold
let return_ens (a : Type) (x : a) : ens_t a return_req
  = fun res -> res == x

let return_ (a : Type) (x : a) : repr a return_req (return_ens a x)
  = fun res -> res == x

(** bind *)

unfold
let bind_req (#a : Type)
      (req_f : req_t)     (ens_f : ens_t a req_f)
      (req_g : a -> req_t)
  : req_t
  = req_f /\ (forall (x : a) . ens_f x ==> req_g x)

unfold
let bind_ens (#a : Type) (#b : Type)
      (req_f : req_t)     (ens_f : ens_t a req_f)
      (req_g : a -> req_t) (ens_g : (x:a) -> ens_t b (req_g x))
  : ens_t b (bind_req req_f ens_f req_g)
  = fun (y : b) ->
      exists (x : a) . ens_f x /\ ens_g x y

let bind (a : Type) (b : Type)
      (#req_f : req_t)     (#ens_f : ens_t a req_f)
      (#req_g : a -> req_t) (#ens_g : (x:a) -> ens_t b (req_g x))
      (f : repr a req_f ens_f) (g : (x:a) -> repr b (req_g x) (ens_g x))
  : repr b (bind_req req_f ens_f req_g) (bind_ens req_f ens_f req_g ens_g)
  = fun (y : b) -> exists (x : a) . ens_f x /\ ens_g x y


unfold
let subcomp_pre (#a : Type)
      (req_f : req_t) (ens_f : ens_t a req_f)
      (req_g : req_t) (ens_g : ens_t a req_g)
  : pure_pre
  = req_g ==> (req_f /\
             (forall (x : a) . ens_f x ==> ens_g x))

let subcomp (a : Type)
      (req_f : req_t) (ens_f : ens_t a req_f)
      (req_g : req_t) (ens_g : ens_t a req_g)
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
  = (p  ==> req_then) /\ (~p ==> req_else)

unfold
let if_then_else_ens (#a : Type)
      (req_then : req_t) (ens_then : ens_t a req_then)
      (req_else : req_t) (ens_else : ens_t a req_else)
      (p : Type0)
  : ens_t a (if_then_else_req req_then req_else p)
  = fun (x : a) ->
      (p  ==> ens_then x) /\ (~p ==> ens_else x)

let if_then_else (a : Type)
      (#req_then : req_t) (#ens_then : ens_t a req_then)
      (#req_else : req_t) (#ens_else : ens_t a req_else)
      (f : repr a req_then ens_then)
      (g : repr a req_else ens_else)
      (p : bool)
  = repr a (if_then_else_req req_then req_else p)
           (if_then_else_ens req_then ens_then req_else ens_else p)

reflectable
effect {
  ND (a : Type) (req : req_t) (ens : ens_t a req)
  with {
    repr;
    return = return_;
    bind;
    subcomp;
    if_then_else
  }
}


unfold
let bind_pure_nstate_req (#a : Type) (wp : pure_wp a)
      (req : a -> req_t)
  : req_t
  = wp (fun x -> req x) /\ True

unfold
let bind_pure_nstate_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (req : a -> req_t) (ens : (x : a) -> ens_t b (req x))
  : ens_t b (bind_pure_nstate_req wp req)
  = fun (y : b) -> as_requires wp /\
      (exists (x : a) . as_ensures wp x /\ (FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp; ens x y))

let bind_pure_nstate (a : Type) (b : Type)
      (#wp : pure_wp a)
      (req : a -> req_t) (ens : (x : a) -> ens_t b (req x))
      (f : eqtype_as_type unit -> PURE a wp) (g : (x : a) -> repr b (req x) (ens x))
  : repr b (bind_pure_nstate_req wp req) (bind_pure_nstate_ens wp req ens)
  = 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun (y : b) ->
      let x = f () in
      g x y

#push-options "--warn_error -330"  //turn off the experimental feature warning
polymonadic_bind (PURE, ND) |> ND = bind_pure_nstate
#pop-options


let return (#a : Type) (x : a) : ND a (requires True) (ensures fun res -> res == x)
  = ND?.reflect (return_ a x)

let most_general (a : Type) (req : req_t) (ens : ens_t a req) : ND a req ens
  = ND?.reflect ((fun (x : a) -> ens x) <: (x : a) -> Pure prop (requires req) (ensures fun p -> p ==> ens x))

let most_general_wp (a : Type) (wp : pure_wp a)
  : ND a (requires as_requires wp /\ True) (ensures fun x -> as_ensures wp x)
  = most_general a (as_requires wp /\ True) (fun x -> as_ensures wp x)

let any_st (a : Type) (p : a -> prop) : ND a (requires True) (ensures p)
  = most_general a True p

let any (a : Type) : ND a (requires True) (ensures fun _ -> True)
  = most_general a True (fun _ -> True)
