module Experiment.Steel.Reify

module Uv = FStar.Universe

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

#set-options "--ide_id_info_off"

assume val some_ref : ref nat
unfold let vp = vptr some_ref
let sl_t = Ghost.erased nat
type req_t = sl_t -> prop
type ens_t (a : Type) = sl_t -> a -> sl_t -> prop
type repr_steel_t (a : Type) (req : req_t) (ens : ens_t a) : Type
  = unit -> Steel a vp (fun _ -> vp) (requires fun h0 -> req (h0 vp)) (ensures fun h0 x h1 -> ens (h0 vp) x (h1 vp))


noeq
type steel_reif : (a : Type u#a) -> Type u#(a+1) =
  | Rspec  : (a : Type) -> (req : req_t) -> (ens : ens_t a) ->
             steel_reif a
  | Rret   : (a : Type) -> (x : a) -> steel_reif a
  | Rbind  : (a : Type u#a) -> (b : Type u#a) ->
             (f : steel_reif a) -> (g : a -> steel_reif b) ->
             steel_reif b
  | RbindP : (a : Type u#a) -> (b : Type) ->
             (wp : pure_wp a) -> (g : a -> steel_reif b) ->
             steel_reif b


/// lifting steel_reif

let raise_pure_wp' (#a : Type u#a) (wp : pure_wp' a) : pure_wp' (Uv.raise_t u#a u#b a)
  = fun pt -> wp (fun x -> pt (Uv.raise_val x))

unfold
let raise_pure_wp (#a : Type u#a) (wp : pure_wp a) : pure_wp (Uv.raise_t u#a u#b a)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    FStar.Monotonic.Pure.as_pure_wp (raise_pure_wp' #a wp)

(* from Steel.Reference.fst *)
let raise_val_inj (#a : Type) (x y : a)
  : Lemma (requires Uv.raise_val x == Uv.raise_val y)
          (ensures x == y)
          [SMTPat (Uv.raise_val x == Uv.raise_val y)]
  =
    Uv.downgrade_val_raise_val x;
    Uv.downgrade_val_raise_val y

let raise_pure_wp_iff (#a : Type u#a) (wp : pure_wp a)
      (pt : pure_post a) (pt' : pure_post (Uv.raise_t u#a u#b a))
  : Lemma (requires forall (x : a) . pt' (Uv.raise_val u#a u#b x) <==> pt x)
          (ensures  raise_pure_wp u#a u#b wp pt' <==> wp pt)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp


let as_ensures' (#a : Type) (wp : pure_wp a) = as_ensures wp

let raise_pure_wp_as_ensures (#a : Type u#a) (wp : pure_wp a) (x : Uv.raise_t u#a u#b a)
  : Lemma (as_ensures' (raise_pure_wp u#a u#b wp) x <==> as_ensures' wp (Uv.downgrade_val u#a u#b x))
    [SMTPat (as_ensures' (raise_pure_wp u#a u#b wp) x)]
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp

let rec raise_steel_reif (#a : Type u#a) (r : steel_reif a)
  : Tot (steel_reif (Uv.raise_t u#a u#b a)) (decreases r)
  = match r with
  | Rspec  a req ens -> Rspec  _ req (fun sl0 x sl1 -> ens sl0 (Uv.downgrade_val x) sl1)
  | Rret   a x       -> Rret   _ (Uv.raise_val x)
  | Rbind  a b f g   -> Rbind  _ _ (raise_steel_reif f) (fun x -> raise_steel_reif (g (Uv.downgrade_val x)))
  | RbindP a b wp g  -> RbindP _ _ (raise_pure_wp wp) (fun x -> raise_steel_reif (g (Uv.downgrade_val x)))

let rbind (a : Type u#a) (b : Type u#b)
      (f : steel_reif a) (g : a -> steel_reif b)
  : steel_reif u#(max a b) (Uv.raise_t b)
  = Rbind _ _ (raise_steel_reif u#a u#b f) (fun x -> raise_steel_reif u#b u#a (g (Uv.downgrade_val x)))

let rbindP (a : Type u#a) (b : Type u#b)
      (wp : pure_wp a) (g : a -> steel_reif b)
  : steel_reif u#(max a b) (Uv.raise_t b)
  = RbindP _ _ (raise_pure_wp u#a u#b wp) (fun x -> raise_steel_reif u#b u#a (g (Uv.downgrade_val x)))


(*** requires / ensures *)

(** return *)

unfold
let return_req : req_t
  = fun _ -> True

unfold
let return_ens (#a : Type) (x : a) : ens_t a
  = fun sl0 r sl1 ->
      r == x /\ sl1 == sl0

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

(** bind_pure *)

unfold
let bind_pure_req (#a : Type) (wp : pure_wp a)
      (req : a -> req_t)
  : req_t
  = fun sl0 -> wp (fun x -> req x sl0) /\ True

unfold
let bind_pure_ens (#a : Type) (#b : Type)
      (wp : pure_wp a)
      (ens : a -> ens_t b)
  : ens_t b
  = fun sl0 y sl1 -> as_requires wp /\ (exists (x:a) . as_ensures wp x /\ ens x sl0 y sl1)

(** reification *)

let rec reif_req (#a : Type) (r : steel_reif a)
  : Tot req_t (decreases r) =
  match r with
  | Rspec  _ req _  -> req
  | Rret   _ _      -> return_req
  | Rbind  _ _ f g  -> bind_req (reif_req f) (reif_ens f) (fun x -> reif_req (g x))
  | RbindP _ _ wp g -> bind_pure_req wp (fun x -> reif_req (g x))
and reif_ens (#a : Type) (r : steel_reif a)
  : Tot (ens_t a) (decreases r) =
  match r with
  | Rspec  _ _ ens  -> ens
  | Rret   _ x      -> return_ens x
  | Rbind  _ _ f g  -> bind_ens (reif_req f) (reif_ens f) (fun x -> reif_ens (g x))
  | RbindP _ _ wp g -> bind_pure_ens wp (fun x -> reif_ens (g x))


open FStar.Calc
open FStar.Classical.Sugar
module T = FStar.Tactics

let iff_refl (a b : Type0) :
  Lemma (requires a == b) (ensures a <==> b)
  = ()

/// [reif_req] and [reif_ens] are not affected by [raise_steel_reif]:

let rec raise_steel_reif_req (#a : Type u#a) (r : steel_reif a) (sl0 : sl_t)
  : Lemma (ensures reif_req (raise_steel_reif u#a u#b r) sl0 <==> reif_req r sl0)
          (decreases r)
  = match r with
  | Rspec _ _ _ | Rret _ _ -> ()
  | Rbind a b f g ->
          assert_norm (
            reif_req (Rbind a b f g) sl0
          == (
            reif_req f sl0 /\
            (forall (x : a) (sl1 : sl_t) . reif_ens f sl0 x sl1 ==> reif_req (g x) sl1)
          ));
          assert_norm (
            reif_req (raise_steel_reif u#a u#b (Rbind a b f g)) sl0
          == (
            reif_req (raise_steel_reif f) sl0 /\
            (forall (x : Uv.raise_t u#a u#b a) (sl1 : sl_t) .
              reif_ens (raise_steel_reif f) sl0 x sl1 ==>
              reif_req (raise_steel_reif (g (Uv.downgrade_val x))) sl1)
          ));
          raise_steel_reif_req f sl0;
          FStar.Classical.forall_intro_2 (raise_steel_reif_ens f sl0);
          FStar.Classical.forall_intro_2 (fun x sl1 -> raise_steel_reif_req (g x) sl1)
  | RbindP a b wp g ->
          let pt  (x : a) = reif_req (g x) sl0 in
          let pt' (x : Uv.raise_t u#a u#b a) =
              reif_req (raise_steel_reif u#a u#b (g (Uv.downgrade_val x))) sl0 in
          (* need to prove it here since tactics in calc do not seem to have acess to the local context *)
          assert (reif_req (RbindP a b wp g) sl0 == (wp pt /\ True)) by T.(trefl ());
          assert (
            reif_req (raise_steel_reif u#a u#b (RbindP a b wp g)) sl0 <==>
            ((raise_pure_wp u#a u#b wp) pt' /\ True)
          ) by T.(apply_lemma (`iff_refl); trefl ());
          
          introduce forall (x : a) . reif_req (raise_steel_reif u#a u#b (g x)) sl0 <==> reif_req (g x) sl0
            with raise_steel_reif_req (g x) sl0;
          raise_pure_wp_iff u#a u#b wp pt pt';
          assert ((raise_pure_wp u#a u#b wp pt' /\ True) <==> (wp pt /\ True));

          calc (<==>) {
            reif_req (raise_steel_reif u#a u#b (RbindP a b wp g)) sl0;
          <==> { (* TODO : use == *) }
            ((raise_pure_wp u#a u#b wp) pt' /\ True);
          <==> {}
            (wp pt /\ True);
          == {}
            reif_req (RbindP a b wp g) sl0;
          }
          
and raise_steel_reif_ens (#a : Type u#a) (r : steel_reif a) (sl0 : sl_t) (x : a) (sl1 : sl_t)
  : Lemma (ensures reif_ens (raise_steel_reif u#a u#b r) sl0 (Uv.raise_val x) sl1 <==> reif_ens r sl0 x sl1)
          (decreases r)
  = match r with
  | Rspec _ _ _ | Rret _ _ -> ()
  | Rbind a b f g ->
          assert_norm (
              reif_ens (Rbind a b f g) sl0 x sl1
            ==
              (reif_req f sl0 /\
              (exists (x' : a) (sl' : sl_t) .
                reif_ens f sl0 x' sl' /\ reif_ens (g x') sl' x sl1))
          );
          assert_norm (
              reif_ens (raise_steel_reif u#a u#b (Rbind a b f g)) sl0 (Uv.raise_val x) sl1
            ==
              (reif_req (raise_steel_reif f) sl0 /\
              (exists (x' : Uv.raise_t u#a u#b a) (sl' : sl_t) .
                reif_ens (raise_steel_reif f) sl0 x' sl' /\
                reif_ens ((raise_steel_reif u#a u#b (g (Uv.downgrade_val x')))) sl' (Uv.raise_val x) sl1))
          );
          raise_steel_reif_req f sl0;
          FStar.Classical.forall_intro_2 (raise_steel_reif_ens f sl0);
          introduce forall (x' : a) (sl' : sl_t) .
            reif_ens (raise_steel_reif u#a u#b (g x')) sl' (Uv.raise_val x) sl1 <==> reif_ens (g x') sl' x sl1
            with raise_steel_reif_ens (g x') sl' x sl1
  | RbindP a b wp g ->
          assert_norm (
            reif_ens (RbindP a b wp g) sl0 x sl1
          ==
            (as_requires wp /\ (exists (x' : a) . as_ensures' wp x' /\ reif_ens (g x') sl0 x sl1))
          );
          assert_norm (
            reif_ens (raise_steel_reif u#a u#b (RbindP a b wp g)) sl0 (Uv.raise_val x) sl1
          ==
            (as_requires wp /\ (exists (x' : Uv.raise_t u#a u#b a) .
              as_ensures' (raise_pure_wp u#a u#b wp) x' /\
              reif_ens (raise_steel_reif (g (Uv.downgrade_val x'))) sl0 (Uv.raise_val x) sl1))
          );
          introduce forall (x' : a) .
            reif_ens (raise_steel_reif (g x')) sl0 (Uv.raise_val x) sl1 <==> reif_ens (g x') sl0 x sl1
            with raise_steel_reif_ens (g x') sl0 x sl1;

          assert (forall (x' : a) .
              as_ensures' wp x' ==> as_ensures' wp (Uv.downgrade_val u#a u#b (Uv.raise_val u#a u#b x')))
  

(*** SteelReif effect *)

/// Not working because of universes issues

type repr (a : Type) (r : steel_reif a) =
  repr_steel_t a (reif_req r) (reif_ens r)

let reif_of_steel (#a : Type) (#req : req_t) (#ens : ens_t a) (f : repr_steel_t a req ens)
  : steel_reif a
  = Rspec a req ens

let repr_of_steel (#a : Type) (#req : req_t) (#ens : ens_t a) (f : repr_steel_t a req ens)
  : repr a (reif_of_steel f)
  = f

let repr_to_steel (#a : Type) (#r : steel_reif a) (f : repr a r)
  : repr_steel_t a (reif_req r) (reif_ens r)
  = f


let return_ (a : Type) (x : a)
  : repr a (Rret a x)
  = fun () -> return x

let elim_reif_req_bind (#a : Type u#a) (#b : Type u#b) (rf : steel_reif a) (rg : a -> steel_reif b) (sl0 : sl_t)
  : Lemma (requires reif_req (rbind a b rf rg) sl0)
          (ensures  reif_req rf sl0 /\
                    (forall (x : a) (sl1 : sl_t) . reif_ens rf sl0 x sl1 ==> reif_req (rg x) sl1))
  = assert_norm (reif_req (rbind a b rf rg) sl0 == (
      reif_req (raise_steel_reif rf) sl0 /\
      (forall (x : Uv.raise_t u#a u#b a) (sl1 : sl_t) .
        reif_ens (raise_steel_reif rf) sl0 x sl1 ==>
        reif_req (raise_steel_reif (rg (Uv.downgrade_val x))) sl1)
    ));
    raise_steel_reif_req u#a u#b rf sl0;
    FStar.Classical.forall_intro_2 (raise_steel_reif_ens u#a u#b rf sl0);
    introduce forall (x : a) (sl1 : sl_t) .
      reif_req (raise_steel_reif u#b u#a (rg x)) sl1 ==> reif_req (rg x) sl1
      with raise_steel_reif_req (rg x) sl1

let intro_reif_ens_bind (#a : Type u#a) (#b : Type u#b) (rf : steel_reif a) (rg : a -> steel_reif b)
      (sl0 : sl_t) (x : a) (sl1 : sl_t) (y : b) (sl2 : sl_t)
  : Lemma (requires reif_req rf sl0 /\
                    reif_ens rf sl0 x sl1 /\
                    reif_ens (rg x) sl1 y sl2)
          (ensures  reif_ens (rbind a b rf rg) sl0 (Uv.raise_val u#b u#a y) sl2)
  = assert_norm (reif_ens (rbind a b rf rg) sl0 (Uv.raise_val u#b u#a y) sl2 == (
      reif_req (raise_steel_reif rf) sl0 /\
        (exists (x : Uv.raise_t u#a u#b a) (sl1 : sl_t) .
          reif_ens (raise_steel_reif rf) sl0 x sl1 /\
          reif_ens (raise_steel_reif (rg (Uv.downgrade_val x))) sl1 (Uv.raise_val u#b u#a y) sl2)
    ));
    raise_steel_reif_req u#a u#b rf sl0;
    raise_steel_reif_ens u#a u#b rf sl0 x sl1;
    raise_steel_reif_ens u#b u#a (rg x) sl1 y sl2

let bind (a : Type u#a) (b : Type u#b)
      (rf : steel_reif a) (rg : a -> steel_reif b)
      (f  : repr a rf)    (g  : (x:a) -> repr b (rg x))
  : repr (Uv.raise_t u#b u#a b) (rbind a b rf rg)
  = fun () -> (**) let sl0 = gget vp in
           (**) elim_reif_req_bind rf rg sl0;
           let x = f () in
           (**) let sl1 = gget vp in
           let y = g x () in
           (**) let sl2 = gget vp in
           (**) intro_reif_ens_bind rf rg sl0 x sl1 y sl2;
           return (Uv.raise_val u#b u#a y)

let subcomp_pre (#a : Type) (rf : steel_reif a) (rg : steel_reif a)
  : pure_pre
  = rf == rg

let subcomp (a : Type) (#rf : steel_reif a) (#rg : steel_reif a)
      (f : repr a rf)
  : Pure (repr a rg) (requires subcomp_pre rf rg) (ensures fun _ -> True)
  = f
(*
//#push-options "--print_universes --print_bound_var_types"
// Type u#(max uu___0 uu___1) is not equal to the expected type Type u#uu___1
[@@allow_informative_binders]
total reflectable reifiable
effect {
  SteelReif (a : Type) (reif : steel_reif a)
  with {
    repr;
    return = return_;
    bind;
    subcomp
  }
}
//#pop-options
*)
