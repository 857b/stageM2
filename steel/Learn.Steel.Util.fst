module Learn.Steel.Util

module G = FStar.Ghost
module Mem = Steel.Memory

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic
open FStar.Classical.Sugar
open Steel.FractionalPermission
open Steel.Reference

#set-options "--ide_id_info_off"

let pts_to_ref_injective_and
      (#a:Type u#0) (r:ref a)
      (p:perm)   (v0 v1:a) (m:mem)
  : Lemma
    (requires interp (pts_to_sl r p v0) m /\ interp (pts_to_sl r p v1) m)
    (ensures  v0 == v1)
  = pts_to_witinv r p;
    Mem.elim_wi (pts_to_sl r p) v0 v1 m

let return_ghost (#a:Type u#a) (#opened:inames)
  (#p:a -> vprop)
  (x:a)
  : SteelGhostBase a true opened Unobservable
         (return_pre (p x)) p
         (return_req (p x)) (return_ens a x p)
  = SteelGhostBase?.reflect (return_ a x opened #p)

let noop_p (#opened) (p : vprop)
  : SteelGhost unit opened p (fun () -> p) (fun _ -> True) (fun h0 () h1 -> frame_equalities p h0 h1)
  = noop ()

(* [vexists] *)
(* TODO? $args *)

let vexists_indep (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Tot prop
  = forall (x0 x1 : a) (m : mem) .
      interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m ==>
      f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)

let vexists_indepD (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t) 
                   (x0 x1 : a) (m : mem)
  : Lemma (requires vexists_indep #a v #t f /\
                    interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
          (ensures  f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m))
  = ()

let vexists_indepI (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  (prf : (x0 : a) -> (x1 : a) -> (m : mem) ->
         Lemma (requires interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
               (ensures  f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)))
  : Lemma (ensures vexists_indep #a v #t f)
  = 
    introduce forall (x0 x1 : a) (m : mem) . interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m ==>
                                        f x0 (sel_of (v x0) m) == f x1 (sel_of (v x1) m)
      with introduce _ ==> _
      with _ . prf x0 x1 m

let vexists_indepI_unique (#a : Type) (v : a -> vprop)
  (prf : (x0 : a) -> (x1 : a) -> (m : mem) ->
         Lemma (requires interp (hp_of (v x0)) m /\ interp (hp_of (v x1)) m)
               (ensures  x0 == x1))
  : Lemma (ensures forall (t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                   . {:pattern (vexists_indep #a v #t f)}
                     vexists_indep #a v #t f)
  = introduce forall t f . vexists_indep #a v #t f
      with vexists_indepI #a v #t f prf


let vexists_sl (#a : Type) (v : a -> vprop)
  : slprop
  = Mem.h_exists #a (fun x -> hp_of (v x))

let vexists_sel' (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> t_of (v x) -> GTot t)
  : selector' t (vexists_sl #a v)
  = fun m ->
      let x = Mem.id_elim_exists (fun x -> hp_of (v x)) m in
      f x (sel_of (v x) m)

let vexists_sel_depends_only_on
      (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> t_of (v x) -> GTot t)
      (_ : squash (vexists_indep v f))
      (m0 : Mem.hmem (vexists_sl v)) (m1 : mem{disjoint m0 m1})
  : Lemma (vexists_sel' v f m0 == vexists_sel' v f (join m0 m1))
  =
    let x0 = G.reveal (Mem.id_elim_exists (fun x -> hp_of (v x))      m0     )  in
    let x1 = G.reveal (Mem.id_elim_exists (fun x -> hp_of (v x)) (join m0 m1))  in
    calc (==) {
      vexists_sel' v f m0;
    == {}
      f x0 (sel_of (v x0) m0);
    == {(* [sel_depends_only_on (sel_of (v x0))] *)}
      f x0 (sel_of (v x0) (join m0 m1));
    == { vexists_indepD v f x0 x1 (join m0 m1)}
      f x1 (sel_of (v x1) (join m0 m1));
    == {}
      vexists_sel' v f (join m0 m1);
    }

let vexists_sel_depends_only_on_core
      (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> t_of (v x) -> GTot t)
      (_ : squash (vexists_indep v f))
      (m0 : Mem.hmem (vexists_sl v))
  : Lemma (ensures  vexists_sel' v f m0 == vexists_sel' v f (core_mem m0))
  =
    let x0 = G.reveal (Mem.id_elim_exists (fun x -> hp_of (v x))      m0     )  in
    let x1 = G.reveal (Mem.id_elim_exists (fun x -> hp_of (v x)) (core_mem m0)) in
    calc (==) {
      vexists_sel' v f m0;
    == {}
      f x0 (sel_of (v x0) m0);
    == {(* [sel_depends_only_on_core (sel_of (v x0))] *)}
      f x0 (sel_of (v x0) (core_mem m0));
    == { vexists_indepD v f x0 x1 (core_mem m0)}
      f x1 (sel_of (v x1) (core_mem m0));
    == {}
      vexists_sel' v f (core_mem m0);
    }

let vexists_sel (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure (selector t (vexists_sl #a v))
         (requires vexists_indep v f) (ensures fun _ -> True)
  =
    Classical.forall_intro_2 (vexists_sel_depends_only_on      v f ());
    Classical.forall_intro   (vexists_sel_depends_only_on_core v f ());
    vexists_sel' v f

[@__steel_reduce__]
let vexists' (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure vprop' (requires vexists_indep v f) (ensures fun _ -> True)
  = {
    hp  = vexists_sl  v;
    t   = t;
    sel = vexists_sel v f
  }

[@__steel_reduce__]
let vexists (#a : Type) (v : a -> vprop) (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
  : Pure vprop (requires vexists_indep v f) (ensures fun _ -> True)
  = VUnit (vexists' v f)


let intro_vexists_lem (#a : Type) (x : a) (v : a -> vprop)
                      (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                      (m : mem)
  : Lemma (requires vexists_indep v f /\
                    interp (hp_of (v x)) m)
          (ensures  interp (hp_of (vexists v f)) m /\
                    vexists_sel v f m == f x (sel_of (v x) m))
  =
    intro_h_exists x (fun x -> hp_of (v x)) m;
    let x' = G.reveal (Mem.id_elim_exists (fun x -> hp_of (v x)) m) in
    calc (==) {
      vexists_sel v f m;
    == {}
      f x' (sel_of (v x') m);
    == {vexists_indepD v f x x' m}
      f x  (sel_of (v x) m);
    }

let intro_vexists (#a : Type) #opened (x : a) (v : a -> vprop)
                  (#t : Type) (f : ((x:a) -> normal (t_of (v x)) -> GTot t) {vexists_indep v f})
  : SteelGhost  unit opened
               (v x)      (fun () -> vexists v f)
               (fun _ -> True) (fun h0 () h1 -> h1 (vexists v f) == f x (h0 (v x)))
  = change_slprop_rel
      (v x) (vexists v f)
      (fun y z -> z == f x y)
      (intro_vexists_lem x v f)

let witness_vexists_lem (#a : Type) (v : a -> vprop)
                        (#t : Type) (f : (x:a) -> normal (t_of (v x)) -> GTot t)
                        (m : mem)
  : Ghost  a
          (requires vexists_indep v f /\
                    interp (hp_of (vexists v f)) m)
          (ensures fun x ->
                    interp (hp_of (v x)) m /\
                    vexists_sel v f m == f x (sel_of (v x) m))
  =
    Mem.id_elim_exists (fun x -> hp_of (v x)) m

let witness_vexists (#a : Type) #opened (v : a -> vprop)
                    (#t : Type) (f : ((x:a) -> normal (t_of (v x)) -> GTot t) {vexists_indep v f})
  : SteelGhost (G.erased a) opened
               (vexists v f) (fun x -> v x)
               (fun _ -> True)    (fun h0 x h1 -> h0 (vexists v f) == f x (h1 (v x)))
  =
    let z : G.erased t = gget (vexists v f) in
    let rfn (x : a) (y : t_of (v x)) : prop = G.reveal z == f x y in
    let lem (m : mem) : Lemma
      (requires interp (hp_of (vexists v f)) m /\ sel_of (vexists v f) m == G.reveal z)
      (ensures  interp (hp_of (h_exists #a (fun x -> v x `vrefine` rfn x))) m)
      = let x = witness_vexists_lem v f m in
        interp_vrefine_hp (v x) (rfn x) m;
        assert (interp (hp_of (v x `vrefine` rfn x)) m);
        Mem.intro_h_exists x (fun x -> hp_of (v x `vrefine` rfn x)) m;
        assert_norm (interp (hp_of (h_exists #a (fun x -> v x `vrefine` rfn x))) m
                  <==> interp (Mem.h_exists #a (fun x -> hp_of (v x `vrefine` rfn x))) m)
    in
    change_slprop
      (vexists v f) (h_exists #a (fun x -> v x `vrefine` rfn x))
      z () lem;
    let x : G.erased a = witness_exists () in
    elim_vrefine (v x) (rfn x);
    x
