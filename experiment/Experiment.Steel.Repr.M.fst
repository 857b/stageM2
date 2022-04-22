module Experiment.Steel.Repr.M

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

#set-options "--ide_id_info_off"

irreducible let __tree_reduce__ : unit = ()

assume val some_ref : ref nat
unfold let vp = vptr some_ref
let sl_t = Ghost.erased nat
type req_t = sl_t -> prop
type ens_t (a : Type) = sl_t -> a -> sl_t -> prop
type repr_steel_t (a : Type) (req : req_t) (ens : ens_t a) : Type
  = unit -> Steel a vp (fun _ -> vp) (requires fun h0 -> req (h0 vp)) (ensures fun h0 x h1 -> ens (h0 vp) x (h1 vp))

noeq
type prog_tree : (a : Type u#a) -> Type u#(a+1) =
  | Tspec  : (a : Type) -> (req : req_t) -> (ens : ens_t a) ->
             prog_tree a
  | Tret   : (a : Type) -> (x : a) -> prog_tree a
  | Tbind  : (a : Type u#a) -> (b : Type u#a) ->
             (f : prog_tree a) -> (g : a -> prog_tree b) ->
             prog_tree b
  | TbindP : (a : Type u#a) -> (b : Type) ->
             (wp : pure_wp a) -> (x : unit -> PURE a wp) -> (g : a -> prog_tree b) ->
             prog_tree b


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

(** prog_tree *)

let rec tree_req (#a : Type) (r : prog_tree a)
  : Tot req_t (decreases r) =
  match r with
  | Tspec  _ req _    -> req
  | Tret   _ _        -> return_req
  | Tbind  _ _ f g    -> bind_req (tree_req f) (tree_ens f) (fun x -> tree_req (g x))
  | TbindP _ _ wp _ g -> bind_pure_req wp (fun x -> tree_req (g x))
and tree_ens (#a : Type) (r : prog_tree a)
  : Tot (ens_t a) (decreases r) =
  match r with
  | Tspec  _ _ ens    -> ens
  | Tret   _ x        -> return_ens x
  | Tbind  _ _ f g    -> bind_ens (tree_req f) (tree_ens f) (fun x -> tree_ens (g x))
  | TbindP _ _ wp _ g -> bind_pure_ens wp (fun x -> tree_ens (g x))


(*** "Monad" *)

/// We define a "monad" (which does not satisfy the monad laws) on a [repr] type which contains a representation
/// of the program as a tree and a corresponding steel function.

noeq
type repr (a : Type) = {
  repr_tree  : prog_tree a;
  repr_steel : repr_steel_t a (tree_req repr_tree) (tree_ens repr_tree)
}

let tree_of_steel (#a : Type) (#req : req_t) (#ens : ens_t a) ($f : repr_steel_t a req ens)
  : prog_tree a
  = Tspec a req ens

[@@ __tree_reduce__]
let repr_of_steel (#a : Type) (#req : req_t) (#ens : ens_t a) ($f : repr_steel_t a req ens)
  : repr a
  = {
    repr_tree  = tree_of_steel f;
    repr_steel = f
  }

[@@ __tree_reduce__]
let return (#a : Type) (x :a)
  : repr a
  = {
    repr_tree  = Tret a x;
    repr_steel = (fun () -> Steel.Effect.Atomic.return x)
  }

let elim_tree_req_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b) (sl0 : sl_t)
  : Lemma (requires tree_req (Tbind a b f g) sl0)
          (ensures  tree_req f sl0 /\
                    (forall (x : a) (sl1 : sl_t) . tree_ens f sl0 x sl1 ==> tree_req (g x) sl1))
  = assert_norm (tree_req (Tbind a b f g) sl0 == (
      tree_req f sl0 /\
      (forall (x : a) (sl1 : sl_t) . tree_ens f sl0 x sl1 ==> tree_req (g x) sl1)
    ))

let intro_tree_ens_bind (#a #b : Type) (f : prog_tree a) (g : a -> prog_tree b)
      (sl0 : sl_t) (x : a) (sl1 : sl_t) (y : b) (sl2 : sl_t)
  : Lemma (requires tree_req f sl0 /\
                    tree_ens f sl0 x sl1 /\
                    tree_ens (g x) sl1 y sl2)
          (ensures  tree_ens (Tbind a b f g) sl0 y sl2)
  = assert_norm (tree_ens (Tbind a b f g) sl0 y sl2 == (
      tree_req f sl0 /\
        (exists (x : a) (sl1 : sl_t) .
          tree_ens f sl0 x sl1 /\
          tree_ens (g x) sl1 y sl2)
    ))

[@@ __tree_reduce__]
let bind (#a #b : Type)
      (f : repr a) (g : a -> repr b)
  : repr b
  = {
    repr_tree  = Tbind a b f.repr_tree (fun x -> (g x).repr_tree);
    repr_steel = (fun () -> (**) let sl0 = gget vp in
                         (**) elim_tree_req_bind f.repr_tree (fun x -> (g x).repr_tree) sl0;
                         let x = f.repr_steel () in
                         (**) let sl1 = gget vp in
                         let y = (g x).repr_steel () in
                         (**) let sl2 = gget vp in
                         (**) intro_tree_ens_bind f.repr_tree (fun x -> (g x).repr_tree)
                         (**)                     sl0 x sl1 y sl2;
                         Steel.Effect.Atomic.return y)
  }

(* --------------------------- *)

module T = FStar.Tactics

let read_req : req_t   = fun sl0 -> True
let read_ens : ens_t nat = fun sl0 x sl1 -> sl1 == sl0 /\ x == Ghost.reveal sl0
let read ()
  : Steel nat vp (fun _ -> vp)
      (requires fun h0     -> read_req (h0 vp))
      (ensures fun h0 x h1 -> read_ens (h0 vp) x (h1 vp))
  = read some_ref

unfold let r_read : repr nat =
  repr_of_steel #nat #read_req #read_ens read

unfold
let test : repr int =
  x <-- r_read;
  y <-- r_read;
  return (x - y)

irreducible
let print_util (#a : Type) (x : a) : prop = True

let normal_tree_steps : list norm_step = [
    delta_attr [`%__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%Mkrepr?.repr_tree];
    iota; zeta
  ]

//let _ = assert (print_util test.repr_tree) by T.(norm normal_tree_steps; qed ())

(* --------------------------- *)

/// generating a non-deterministic function representing the program tree

module ND = Learn.Effect.NonDeterminism

let cast_nd (#a #b : Type) (#req0 : a -> ND.req_t) (#ens0 : (x:a) -> ND.ens_t b (req0 x))
                           (req1  : a -> ND.req_t) (ens1  : (x:a) -> ND.ens_t b (req1 x))
                           ($f : (x : a) -> ND.ND b (req0 x) (ens0 x))
  : Pure ((x : a) -> ND.ND b (req1 x) (ens1 x))
         (requires forall (x : a) . ND.subcomp_pre (req0 x) (ens0 x) (req1 x) (ens1 x))
         (ensures fun _ -> True)
  = fun x -> f x

[@@ __tree_reduce__]
let rec prog_tree_to_ND (#a : Type) (p : prog_tree a)
  : (sl0 : sl_t) -> ND.ND (a & sl_t) (requires tree_req p sl0) (ensures fun (x, sl1) -> tree_ens p sl0 x sl1)
  = match p with
  | Tspec a req ens   -> (fun sl0 -> ND.most_general (a&sl_t) (req sl0) (fun (x, sl1) -> ens sl0 x sl1))
  | Tret  a x         -> (fun sl0 -> ND.return (x, sl0))
  | Tbind a b f g     -> FStar.Classical.forall_intro (FStar.Classical.move_requires
                          (elim_tree_req_bind f (fun x -> (g x)))); 
                        introduce forall sl0 (x : a) sl1 (y : b) sl2.
                          tree_req f sl0 /\ tree_ens f sl0 x sl1 /\ tree_ens (g x) sl1 y sl2 ==>
                          tree_ens (Tbind a b f g) sl0 y sl2
                          with introduce _ ==> _
                          with _ . intro_tree_ens_bind f (fun x -> (g x)) sl0 x sl1 y sl2;
                        (fun sl0 -> let (x, sl1) = prog_tree_to_ND f sl0 in
                                 prog_tree_to_ND (g x) sl1)
  | TbindP a b wp x g -> FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
                        let req sl0 : ND.req_t =
                          ND.bind_pure_nstate_req wp (fun xv -> tree_req (g xv) sl0) in
                        let ens sl0 : ND.ens_t (b & sl_t) (req sl0) =
                          ND.bind_pure_nstate_ens wp
                               (fun xv -> tree_req (g xv) sl0)
                               (fun xv (y, sl1) -> tree_ens (g xv) sl0 y sl1) in
                        let rt (sl0 : sl_t) :
                          ND.ND (b & sl_t)
                            (requires req sl0)
                            (ensures  ens sl0)
                          = prog_tree_to_ND (g (x ())) sl0
                        in
                        let req' sl0 : ND.req_t = tree_req (TbindP a b wp x g) sl0 in
                        let ens' sl0 : ND.ens_t (b & sl_t) (req' sl0) =
                          fun (y, sl1) -> tree_ens (TbindP a b wp x g) sl0 y sl1 in
                        assert (forall (sl0 : sl_t) . ND.subcomp_pre (req sl0) (ens sl0) (req' sl0) (ens' sl0))
                          by T.(let _ = forall_intro () in
                                let _ = implies_intro () in
                                smt ());
                        cast_nd req' ens' rt

let normal_tree_ND_steps : list norm_step = [
    delta_attr [`%__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%Mkrepr?.repr_tree; `%tree_of_steel];
    iota; zeta_full
  ]

(*
let _ = assert (print_util (prog_tree_to_ND (test.repr_tree)))
          by T.(norm (normal_tree_ND_steps); qed ())
*)
