module Experiment.Steel.Func

module T  = FStar.Tactics
module ND = Learn.Effect.NonDeterminism

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

#set-options "--ide_id_info_off"

irreducible let __func_reduce__ : unit = ()

assume val some_ref : ref nat
unfold let vp = vptr some_ref

let sl_t = Ghost.erased nat

type req_t = sl_t -> prop
type ens_t (a : Type) = sl_t -> a -> sl_t -> prop

(* TODO? Steel.Effect.repr *)
unfold
let repr_steel_t (a : Type) (req : req_t) (ens : ens_t a) : Type
  = unit -> Steel a vp (fun _ -> vp) (requires fun h0 -> req (h0 vp)) (ensures fun h0 x h1 -> ens (h0 vp) x (h1 vp))

unfold
let repr_func (a : Type) (req : req_t) (ens : ens_t a) : Type
  = (sl0 : sl_t) -> ND.ND (a & sl_t) (requires req sl0) (ensures fun (x, sl1) -> ens sl0 x sl1)


type repr (a : Type) (req : req_t) (ens : ens_t a) (func : repr_func a req ens) =
  repr_steel_t a req ens


let repr_of_steel_func (#a : Type) (#req : req_t) (#ens : ens_t a) (f : repr_steel_t a req ens)
  : repr_func a req ens
  = (fun (sl0 : sl_t) -> ND.most_general (a & sl_t) (req sl0) (fun (x, sl1) -> ens sl0 x sl1))

let repr_of_steel (a : Type) (req : req_t) (ens : ens_t a) (f : repr_steel_t a req ens)
  : repr a req ens (repr_of_steel_func f)
  = f


(** return *)

unfold
let return_req : req_t
  = fun _ -> True

unfold
let return_ens (a : Type) (x : a) : ens_t a
  = fun sl0 r sl1 ->
      r == x /\ sl1 == sl0

[@@ __func_reduce__]
let return_func (a : Type) (x : a) : repr_func a return_req (return_ens a x)
  = fun sl0 -> ND.return (x, sl0)

let return_ (a : Type) (x : a)
  : repr a return_req (return_ens a x) (return_func a x)
  = (fun ()  -> return x)

(** bind *)

unfold
let bind_req (#a : Type)
      (req_f : req_t) (ens_f : ens_t a)
      (req_g : a -> req_t)
  : req_t
  = fun sl0 -> req_f sl0 /\
      (forall (x : a) (sl1 : sl_t) .
        ens_f sl0 x sl1 ==> req_g x sl1)

unfold
let bind_ens (#a : Type) (#b : Type)
      (req_f : req_t) (ens_f : ens_t a)
      (ens_g : a -> ens_t b)
  : ens_t b
  = fun sl0 y sl2 ->
      req_f sl0 /\
      (exists (x : a) (sl1 : sl_t) .
        ens_f sl0 x sl1 /\
        ens_g x sl1 y sl2)

let bind_func (a : Type) (b : Type)
      (#req_f : req_t)     (#ens_f : ens_t a)     (ff : repr_func a req_f ens_f)
      (#req_g : a -> req_t) (#ens_g : a -> ens_t b) (gf : (x:a) -> repr_func b (req_g x) (ens_g x))
  : repr_func b (bind_req req_f ens_f req_g) (bind_ens req_f ens_f ens_g)
  = fun sl0 -> let x = ff sl0 in gf x._1 x._2

[@@ __func_reduce__]
let bind (a : Type) (b : Type)
      (#req_f : req_t)     (#ens_f : ens_t a)     (#ff : repr_func a req_f ens_f)
      (#req_g : a -> req_t) (#ens_g : a -> ens_t b) (#gf : (x:a) -> repr_func b (req_g x) (ens_g x))
      (f : repr a req_f ens_f ff)
      (g : (x:a) -> repr b (req_g x) (ens_g x) (gf x))
  : repr b (bind_req req_f ens_f req_g) (bind_ens req_f ens_f ens_g) (bind_func a b ff gf)
  = (fun ()  -> let x = f () in g x ())

(** subcomp *)

let subcomp_pre (#a : Type)
      (req_f : req_t) (ens_f : ens_t a)
      (req_g : req_t) (ens_g : ens_t a)
  : Type0
  = (forall sl0 . req_g sl0 ==> req_f sl0) /\ (forall sl0 x sl1 . ens_f sl0 x sl1 ==> ens_g sl0 x sl1)


irreducible let __subcomp_tac__ : unit = ()

[@@ resolve_implicits; __subcomp_tac__]
let subcomp_tac () : T.Tac unit = T.(
  norm [delta_only [`%subcomp_pre]];
  //dump "subcomp";
  smt ())


[@@ __func_reduce__]
let subcomp_func (a : Type)
      (#req_f : req_t) (#ens_f : ens_t a)
      (#req_g : req_t) (#ens_g : ens_t a)
      (sc_pre : squash (subcomp_pre req_f ens_f req_g ens_g))
      (ff : repr_func a req_f ens_f)
  : repr_func a req_g ens_g
  = (fun sl0 -> ff sl0)

let subcomp (a : Type)
      (#req_f : req_t) (#ens_f : ens_t a)
      (#req_g : req_t) (#ens_g : ens_t a)
      (#ff : repr_func a req_f ens_f)
      (#[@@@ __subcomp_tac__] sc_pre : squash (subcomp_pre req_f ens_f req_g ens_g))
      (f : repr a req_f ens_f ff)
  : Pure (repr a req_g ens_g (subcomp_func a sc_pre ff)) (requires True) (ensures fun _ -> True)
  = f

(** FSteel *)

[@@allow_informative_binders]
total reflectable reifiable
effect {
  FSteel (a : Type) (req : req_t) (ens : ens_t a) (func : repr_func a req ens)
  with {
    repr;
    return = return_;
    bind;
    subcomp
  }
}

(** bind_pure_fsteel *)

unfold
let bind_pure_fsteel_req (#a : Type) (wp : pure_wp a)
      (req : a -> req_t)
  : req_t
  = fun sl0 -> wp (fun x -> req x sl0) /\ True

unfold
let bind_pure_fsteel_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (ens : a -> ens_t b)
  : ens_t b
  = fun sl0 y sl1 -> as_requires wp /\ (exists (x:a) . as_ensures wp x /\ ens x sl0 y sl1)

(*// rejected by polymonadic_bind
[@@ __func_reduce__]
let bind_pure_fsteel_func (a : Type) (b : Type)
      (#wp : pure_wp a)
      (#req : a -> req_t) (#ens : a -> ens_t b)
      (f : eqtype_as_type unit -> PURE a wp) (gf : (x:a) -> repr_func b (req x) (ens x))
  : repr_func b (bind_pure_fsteel_req wp req) (bind_pure_fsteel_ens wp ens)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun sl0 -> let x = f () in gf x sl0
*)
[@@ __func_reduce__]
let bind_pure_fsteel_func (a : Type) (b : Type)
      (wp : pure_wp a)
      (#req : a -> req_t) (#ens : a -> ens_t b)
      (gf : (x:a) -> repr_func b (req x) (ens x))
  : repr_func b (bind_pure_fsteel_req wp req) (bind_pure_fsteel_ens wp ens)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun sl0 -> let x = ND.most_general_wp a wp in gf x sl0

(*assume
val bind_pure_fsteel_func (a : Type) (b : Type)
      (wp : pure_wp a)
      (#req : a -> req_t) (#ens : a -> ens_t b)
      (gf : (x:a) -> repr_func b (req x) (ens x))
  : repr_func b (bind_pure_fsteel_req wp req) (bind_pure_fsteel_ens wp ens)
*)

let bind_pure_fsteel (a : Type) (b : Type)
      (#wp : pure_wp a)
      (#req : a -> req_t) (#ens : a -> ens_t b) (#gf : (x:a) -> repr_func b (req x) (ens x))
      (f : eqtype_as_type unit -> PURE a wp)
      (g : (x:a) -> repr b (req x) (ens x) (gf x))
  : repr b (bind_pure_fsteel_req wp req) (bind_pure_fsteel_ens wp ens) (bind_pure_fsteel_func a b wp gf)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    fun ()  -> let x = f () in g x ()

(*
assume
val bind_pure_fsteel (a : Type) (b : Type)
      (#wp : pure_wp a)
      (#req : a -> req_t) (#ens : a -> ens_t b) (#gf : (x:a) -> repr_func b (req x) (ens x))
      (f : eqtype_as_type unit -> PURE a wp)
      (g : (x:a) -> repr b (req x) (ens x) (gf x))
  : repr b (bind_pure_fsteel_req wp req) (bind_pure_fsteel_ens wp ens) (bind_pure_fsteel_func a b wp gf)
*)

#push-options "--warn_error -330"  //turn off the experimental feature warning
polymonadic_bind (PURE, FSteel) |> FSteel = bind_pure_fsteel
#pop-options

let steelF (#a : Type) (#req : req_t) (#ens : ens_t a) ($f : repr_steel_t a req ens)
  : FSteel a req ens (repr_of_steel_func f)
  = FSteel?.reflect (repr_of_steel a req ens f)

let to_steel (#a : Type) (#req : req_t) (#ens : ens_t a) (#ff : repr_func a req ens)
    (f : unit -> FSteel a req ens ff)
  : Steel a vp (fun _ -> vp) (requires fun h0 -> req (h0 vp)) (ensures fun h0 x h1 -> ens (h0 vp) x (h1 vp))
  = reify (f ()) ()

(* --------------- *)

let fread_req : req_t = fun (sl0 : sl_t) -> True
let fread_ens : ens_t nat = fun (sl0 : sl_t) (x : nat) (sl1 : sl_t) -> sl1 == sl0 /\ x == Ghost.reveal sl0

let fread_steel ()
  : Steel nat vp (fun _ -> vp)
      (requires fun h0 -> fread_req (h0 vp)) (ensures fun h0 x h1 -> fread_ens (h0 vp) x (h1 vp))
  = read some_ref

unfold let fread () : FSteel nat fread_req fread_ens (repr_of_steel_func fread_steel)
  = steelF #nat #fread_req #fread_ens fread_steel

//  module T = FStar.Tactics
//  [@@ handle_smt_goals ]
//  let tac () = T.dump "test"

(*
// Failed to resolve implicit argument of type 'Prims.squash...
unfold let test () : FSteel unit (fun sl0 -> fread_req sl0) (fun _ _ _ -> True) _ =
  let x = fread () in assert (x == x)
  //let y = fread () in
  //assert (x == x)

unfold let test_func = (reify (test ())).repr_func

(*
unfold let fread_repr : repr nat fread_req fread_ens (repr_of_steel_func fread_steel)
  = repr_of_steel nat fread_req fread_ens fread_steel

unfold let test_func : repr unit (fun _ -> True) (fun _ _ _ -> True) =
  subcomp unit begin
  bind nat unit fread_repr (fun x ->
  bind nat unit fread_repr (fun y ->
  return_ unit ()))
  end
*)
irreducible
let print_util (#a : Type) (x : a) : prop = True

let normal_func_steps = [
    delta_attr [`%__func_reduce__];
    delta_qualifier ["unfold"];
    iota;
    reify_
  ]

let _ = assert (print_util test_func)
          by T.(norm normal_func_steps; qed ())
*)
