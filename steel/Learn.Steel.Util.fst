module Learn.Steel.Util

module G = FStar.Ghost
module Mem = Steel.Memory

open Steel.Memory
open Steel.Effect.Common
open Steel.Effect.Atomic
open Steel.Effect
open FStar.Classical.Sugar
open Steel.FractionalPermission
open Steel.Reference

#set-options "--ide_id_info_off"

(* [pure] *)

let pure0 (p : prop) : vprop
  = vrefine emp (fun _ -> p)

let pure_sl  p = hp_of (pure0 p)
let pure_sel p = reveal_emp (); sel_of (pure0 p)

let intro_pure_lem (p : prop) (m : mem)
  : Lemma (requires p) (ensures interp (hp_of (pure p)) m)
  =
    Mem.intro_emp m;
    reveal_emp ();
    interp_vrefine_hp emp (fun _ -> p) m

let elim_pure_lem (p : prop) (m : mem)
  : Lemma (requires Mem.interp (hp_of (pure p)) m) (ensures p)
  =
    interp_vrefine_hp emp (fun _ -> p) m


(* [vopt] *)

let vopt0 (b : bool) (v : vprop) : vprop
  = if b then vrewrite v #(option (t_of v)) Some
    else vrewrite emp #(option (t_of v)) (fun _ -> None)

let vopt_sl  b v = hp_of  (vopt0 b v)
let vopt_sel b v = sel_of (vopt0 b v)
let vopt_eq  b v : squash (vopt b v == expanded_vprop (vopt0 b v)) = ()

let vopt_intro_t #opened (v : vprop)
  : SteelGhost unit opened
      v (fun () -> vopt true v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h1 (vopt true v) == Some (h0 v))
  =
    intro_vrewrite v #(option (t_of v)) Some;
    intro_expanded_vprop (vopt0 true v);
    rewrite_vprop (eq_sym (vopt_eq true v))

let vopt_intro_f #opened (v : vprop)
  : SteelGhost unit opened
      emp (fun () -> vopt false v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h1 (vopt false v) == None)
  =
    intro_vrewrite emp #(option (t_of v)) (fun _ -> None);
    assert_norm (vopt0 false v == vrewrite emp #(option (t_of v)) (fun _ -> None));
    change_equal_slprop (vrewrite emp #(option (t_of v)) (fun _ -> None)) (vopt0 false v);
    intro_expanded_vprop (vopt0 false v);
    rewrite_vprop (eq_sym (vopt_eq false v))

let vopt_elim_t #opened (v : vprop)
  : SteelGhost unit opened
      (vopt true v) (fun () -> v)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h0 (vopt true v) == Some (h1 v))
  =
    rewrite_vprop (vopt_eq true v);
    elim_expanded_vprop (vopt0 true v);
    elim_vrewrite v #(option (t_of v)) Some

let vopt_elim_f #opened (v : vprop)
  : SteelGhost unit opened
      (vopt false v) (fun () -> emp)
      (requires fun _ -> True) (ensures fun h0 () h1 -> h0 (vopt false v) == None)
  =
    rewrite_vprop (vopt_eq false v);
    elim_expanded_vprop (vopt0 false v);
    assert_norm (vopt0 false v == vrewrite emp #(option (t_of v)) (fun _ -> None));
    change_equal_slprop (vopt0 false v) (vrewrite emp #(option (t_of v)) (fun _ -> None));
    elim_vrewrite emp #(option (t_of v)) (fun _ -> None)


(* [vexists] *)
(* TODO? $args *)

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


(* [vdept] *)

let vdept0 (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  : Pure vprop (requires True) (ensures fun vd -> t_of vd == dtuple2 (t_of v) dt)
  = (v `vdep` p) `vrewrite` (fun (|x, y|) -> (|x, y|) <: dtuple2 (t_of v) dt)

let vdept_sl (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  : Mem.slprop
  = hp_of (vdept0 v #dt p)

let vdept_sel (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  : selector (dtuple2 (t_of v) dt) (vdept_sl v #dt p)
  = sel_of (vdept0 v #dt p)

let interp_vdept_sl (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
                    (m: Mem.mem)
  : Lemma Mem.(interp (vdept_sl v #dt p) m
               <==> (interp (hp_of v) m /\ interp (hp_of v `star` hp_of (p (sel_of v m))) m))
  =
    interp_vdep_hp v p m

let vdept_sel_eq (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
                 (m: Mem.hmem (vdept_sl v #dt p))
  : Lemma Mem.(
      interp (hp_of v) m /\
     (let x = sel_of v m in
      interp (hp_of (p x)) m /\
      vdept_sel v p m == (| x, sel_of (p x) m |) ))
  =
    vrewrite_sel_eq (v `vdep` p) (fun (|x, y|) -> (|x, y|) <: dtuple2 (t_of v) dt) m;
    vdep_sel_eq v p m

let intro_vdept (#opened:inames) (v: vprop) (q: vprop)
                (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
  = change_slprop_rel_with_cond
      (v `star` q) (vdept v #dt p)
      (fun (vv, _) -> q == p vv)
      (fun (vv, qv) x2 -> q == p vv /\ dfst #(t_of v) #dt x2 == vv /\ dsnd #(t_of v) #dt x2 == qv)
      (fun m -> interp_vdept_sl v #dt p m;
             vdept_sel_eq v #dt p m)

(* TODO: Why is it necessary ? *)
unfold
let rt_vp (v : vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
          (res : G.erased (t_of v)) : vprop
  = v `star` p (G.reveal res)

let elim_vdept (#opened:inames) (v: vprop) (#dt : t_of v -> Type) ($p : (x:t_of v) -> (v' : vprop {t_of v' == dt x}))
: SteelGhost (G.erased (t_of v)) opened
  (vdept v p) (fun res -> rt_vp v #dt p res)
  (requires fun _ -> True)
  (ensures fun h res h' ->
      let fs = h' v in
      let sn : dt (G.reveal res) = h' (p (G.reveal res)) in
      let x2 = h (vdept v #dt p) in
      G.reveal res == fs /\
      dfst x2 == fs /\
      dsnd x2 == sn)
  =
    let x2  = gget (vdept v p) in
    let res : G.erased (t_of v) = G.hide (dfst #(t_of v) #dt x2) in
    change_slprop_rel_with_cond
      (vdept v p) (v `star` p (G.reveal res))
      (fun x2' -> x2' == G.reveal x2)
      (fun _ (vv, qv) -> vv == G.reveal res /\ qv == dsnd #(t_of v) #dt x2)
      (fun m -> interp_vdept_sl v #dt p m;
             vdept_sel_eq v #dt p m);
    res

