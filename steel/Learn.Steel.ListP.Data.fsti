module Learn.Steel.ListP.Data

module L   = FStar.List.Pure
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.ListP.Param

/// This module defines a parametrized linked list structure.
/// The vprop [mlist p entry len exit] represents a list segment `[entry, exit)` and is indexed by:
/// - the abstract parameter used for the cells of the list
/// - the entry of the list, that is, the address of the first cell
/// - the length of the segment that is represented by the vprop
/// - the exit of the segment, that is, the address the `next` field of the last cell points to
/// The associated selector is a list of [cell_t p], that is a list of references and data.
/// Thanks to the refinement on the selector type, it is guaranted that the list has length [len] and is related to
/// [entry] and [exit].

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

(** intro/elim lemmas *)

/// We only define here the minimal set of intro/elim lemmas. They are defined as pure lemmas that operate on memories.
/// Their stateful SteelGhost equivalents are derived in [Learn.Steel.ListP.Derived].

val intro_mlist_nil_lem (p : list_param) (r0 : ref p.r) (m : Mem.mem)
  : Lemma (ensures Mem.interp (hp_of (mlist p r0 0 r0)) m /\
                   (sel_of (mlist p r0 0 r0) m <: mlist_sel_t p r0 0 r0) == [])

val elim_mlist_nil_lem (p : list_param) (r0 r1 : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist p r0 0 r1)) m)
          (ensures  r0 == r1)

val intro_mlist_cons_lem (p : list_param) (r0 r1 : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (vcell p r0 `star` mlist p r1 len exit)) m /\
                    (p.cell r0).get_next (sel_of (vcell p r0) m) == r1)
          (ensures  Mem.interp (hp_of (mlist p r0 (len+1) exit)) m /\
                    sel_of (mlist p r0 (len+1) exit) m ==
                      (|r0, (p.cell r0).get_data (sel_of (vcell p r0) m)|)
                      :: (sel_of (mlist p r1 len exit) m <: mlist_sel_t p r1 len exit))

val elim_mlist_cons_lem (p : list_param) (r0 : ref p.r)
                        (hd : cell_t p) (tl : list (cell_t p))
                        (len : nat) (exit : ref p.r) (m: Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist p r0 (len + 1) exit)) m /\
                    (sel_of (mlist p r0 (len + 1) exit) m
                      <: mlist_sel_t p r0 (len+1) exit) == hd :: tl)
          (ensures (let r1 = sg_entry tl exit in
                    Mem.interp (hp_of (vcell p r0 `star` mlist p r1 len exit)) m /\
                   (let c0 = sel_of (vcell p r0) m in
                    (p.cell r0).get_next c0 == r1 /\
                    (p.cell r0).get_data c0 == hd._2 /\
                    sel_of (mlist p r1 len exit) m == tl)))
