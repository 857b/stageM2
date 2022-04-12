module Learn.Steel.ListP.Data

module L   = FStar.List.Pure
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.ListP.Param

let sg_entry (#r : Type) (#a : r -> Type) (l : list (x:r & a x)) (exit : r) : r =
  match l with
  | [] -> exit
  | hd :: _ -> hd._1

type mlist_sel_t (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) : Type =
  l : list (cell_t p) {len = L.length l /\ entry == sg_entry l exit}

val mlist_sl (p : list_param u#0) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Mem.slprop u#1

val mlist_sel (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : selector (mlist_sel_t p entry len exit) (mlist_sl p entry len exit)

[@@__steel_reduce__]
let mlist' (p : list_param) (entry : ref p.r) ([@@@smt_fallback] len : nat) (exit : ref p.r) : vprop' =
  {
    hp  = mlist_sl    p entry len exit;
    t   = mlist_sel_t p entry len exit;
    sel = mlist_sel   p entry len exit
  }
unfold let mlist (p : list_param) (entry : ref p.r) ([@@@smt_fallback] len : nat) (exit : ref p.r) : vprop =
  VUnit (mlist' p entry len exit)

[@@ __steel_reduce__]
let sel_list (#q:vprop) (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (mlist p entry len exit) /\ True)})
  : GTot (mlist_sel_t p entry len exit)
  = h (mlist p entry len exit)

(* intro/elim lemmas *)

val intro_mlist_nil_lem (p : list_param) (r0 : ref p.r) (m : Mem.mem)
  : Lemma (ensures Mem.interp (hp_of (mlist p r0 0 r0)) m /\
                   (sel_of (mlist p r0 0 r0) m <: mlist_sel_t p r0 0 r0) == [])

val elim_mlist_nil_lem (p : list_param) (r0 r1 : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist p r0 0 r1)) m)
          (ensures  r0 == r1)

val intro_mlist_cons_lem (p : list_param) (r0 r1 : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of ((p.cell r0).vp `star` mlist p r1 len exit)) m /\
                    (p.cell r0).get_next (sel_of (p.cell r0).vp m) == r1)
          (ensures  Mem.interp (hp_of (mlist p r0 (len+1) exit)) m /\
                    sel_of (mlist p r0 (len+1) exit) m ==
                      (|r0, (p.cell r0).get_data (sel_of (p.cell r0).vp m)|)
                      :: (sel_of (mlist p r1 len exit) m <: mlist_sel_t p r1 len exit))

val elim_mlist_cons_lem (p : list_param) (r0 : ref p.r)
                        (hd : cell_t p) (tl : list (cell_t p))
                        (len : nat) (exit : ref p.r) (m: Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist p r0 (len + 1) exit)) m /\
                    (sel_of (mlist p r0 (len + 1) exit) m
                      <: mlist_sel_t p r0 (len+1) exit) == hd :: tl)
          (ensures (let r1 = sg_entry tl exit in
                    Mem.interp (hp_of ((p.cell r0).vp `star` mlist p r1 len exit)) m /\
                   (let c0 = sel_of (p.cell r0).vp m in
                    (p.cell r0).get_next c0 == r1 /\
                    (p.cell r0).get_data c0 == hd._2 /\
                    sel_of (mlist p r1 len exit) m == tl)))
