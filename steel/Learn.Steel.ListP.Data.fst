module Learn.Steel.ListP.Data

module L   = FStar.List.Pure
module T   = FStar.Tactics
module TP  = Learn.Steel.TProp
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.ListP.Param


(**** Definition of the vprop *)

/// We define [mlist p entry len exit] by induction on [len].
/// We use vprop combiners instead of defining manually the selector.

let rec mlist_tp (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Tot (TP.tprop (mlist_sel_t p entry len exit)) (decreases len)
  = TP.(
    if len = 0
    then begin
      _ <-- tpure (entry == exit);
      return #(mlist_sel_t p entry len exit) []
    end else begin
      c  <-- vprt (t_of (vcell p entry)) (vcell p entry);
      rs <-- tpr (mlist_tp p ((p.cell entry).get_next c) (len - 1) exit);
      return #(mlist_sel_t p entry len exit) ((|entry, (p.cell entry).get_data c|) :: rs)
    end
  )

let mlist_sl (p : list_param) entry len exit =
  (mlist_tp p entry len exit).t_hp

let mlist_sel (p : list_param) entry len exit =
  (mlist_tp p entry len exit).t_sel


(**** Intro/Elim lemmas *)

let rew () = T.norm [delta_only [`%mlist_tp]; zeta]

let intro_mlist_nil_lem (p : list_param) (r0 : ref p.r) (m : Mem.mem)
  =
    let tp = mlist_tp p r0 0 r0 in
    assert (Mem.interp (hp_of (mlist p r0 0 r0)) m /\
            (sel_of (mlist p r0 0 r0) m <: mlist_sel_t p r0 0 r0) == [])
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [1] in smt ())

let elim_mlist_nil_lem (p : list_param) (r0 r1 : ref p.r) (m : Mem.mem)
  =
    let tp = mlist_tp p r0 0 r0 in
    assert (r0 == r1)
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [1] in smt ())

let intro_mlist_cons_lem (p : list_param) (r0 r1 : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  =
    let tp = mlist_tp p r0 (len+1) exit in
    assert (Mem.interp (hp_of (mlist p r0 (len+1) exit)) m /\
            sel_of (mlist p r0 (len+1) exit) m ==
              (|r0, (p.cell r0).get_data (sel_of (vcell p r0) m)|)
              :: (sel_of (mlist p r1 len exit) m <: mlist_sel_t p r1 len exit))
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())

let elim_mlist_cons_lem (p : list_param) (r0 : ref p.r)
                        (hd : cell_t p) (tl : list (cell_t p))
                        (len : nat) (exit : ref p.r) (m: Mem.mem)
  =
    let tp = mlist_tp p r0 (len+1) exit in
    assert (let r1 = sg_entry tl exit in
            Mem.interp (hp_of (vcell p r0 `star` mlist p r1 len exit)) m /\
           (let c0 = sel_of (vcell p r0) m in
            (p.cell r0).get_next c0 == r1 /\
            (p.cell r0).get_data c0 == hd._2 /\
            sel_of (mlist p r1 len exit) m == tl))
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())
