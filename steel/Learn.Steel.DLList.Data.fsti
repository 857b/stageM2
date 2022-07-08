module Learn.Steel.DLList.Data

module U   = Learn.Util
module Mem = Steel.Memory

open FStar.List.Pure
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.DLList.Param


#set-options "--fuel 1 --ifuel 1"

let sg_entry (#p : list_param) (l : list (cell_t p)) (nxt : ref p.r) : ref p.r =
  match l with
  | [] -> nxt
  | hd :: _ -> hd._1

let sg_exit  (#p : list_param) (prv : ref p.r) (l : list (cell_t p)) : ref p.r =
  if Cons? l then (last l)._1 else prv

// ALT: dllist_sel_t' + refinement
noeq
type dllist_sel_t (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) : Type = {
  dll_sg  : llist (cell_t p) len;
  dll_prv : prv : ref p.r { exit  == sg_exit  prv dll_sg };
  dll_nxt : nxt : ref p.r { entry == sg_entry dll_sg nxt };
}

let dllist_sel_t_get_ref
      (#p : list_param) (#entry : ref p.r) (#len : nat) (#exit : ref p.r)
      (sl : dllist_sel_t p entry len exit)
  : Lemma (exit  == sg_exit  sl.dll_prv sl.dll_sg /\
           entry == sg_entry sl.dll_sg  sl.dll_nxt)
  = ()

let dll_nil (#p : list_param) (entry : ref p.r) (exit : ref p.r)
  : dllist_sel_t p entry 0 exit
  = {
    dll_sg  = [];
    dll_prv = exit;
    dll_nxt = entry;
  }

/// [r1] should be [(p.cell r0).get_ref c Forward]
let dll_cons
      (#p : list_param) (#r0 #r1 : ref p.r) (#len' : nat) (#r2 : ref p.r)
      (c : t_of (vcell p r0))
      (sl1 : dllist_sel_t p r1 len' r2 {sl1.dll_prv == r0})
  : GTot (dllist_sel_t p r0 (len' + 1) r2)
  = {
    dll_sg  = (|r0, (p.cell r0).get_data c|) :: sl1.dll_sg;
    dll_prv = (p.cell r0).get_ref c Backward;
    dll_nxt = sl1.dll_nxt;
  }


val dllist_sl (p : list_param u#0) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Mem.slprop u#1

val dllist_sel (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : selector (dllist_sel_t p entry len exit) (dllist_sl p entry len exit)

[@@__steel_reduce__]
let dllist' (p : list_param) (entry : ref p.r) ([@@@smt_fallback] len : nat) (exit : ref p.r) : vprop' =
  {
    hp  = dllist_sl    p entry len exit;
    t   = dllist_sel_t p entry len exit;
    sel = dllist_sel   p entry len exit
  }
unfold let dllist (p : list_param) (entry : ref p.r) ([@@@smt_fallback] len : nat) (exit : ref p.r) : vprop =
  VUnit (dllist' p entry len exit)

[@@ __steel_reduce__]
let sel_dllist (#q:vprop) (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (dllist p entry len exit) /\ True)})
  : GTot (dllist_sel_t p entry len exit)
  = h (dllist p entry len exit)


val dllist_nil_interp (p : list_param) (entry : ref p.r) (exit : ref p.r) (m : Mem.mem)
  : Lemma (Mem.interp (hp_of (dllist p entry 0 exit)) m /\
           (sel_of (dllist p entry 0 exit) m <: dllist_sel_t p entry 0 exit) == dll_nil entry exit)

val dllist_cons_interp (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (Mem.interp (hp_of (dllist p entry (len + 1) exit)) m
         <==> Mem.interp (hp_of (vcell p entry)) m /\
           (let c = sel_of (vcell p entry) m in
            let entry' = (p.cell entry).get_ref c Forward in
            Mem.interp (hp_of (vcell p entry) `Mem.star` hp_of (dllist p entry' len exit)) m /\
           (let sl1 : dllist_sel_t p entry' len exit
                    = sel_of (dllist p entry' len exit) m in
            sl1.dll_prv == entry)))

val dllist_cons_sel_eq
      (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (dllist p entry (len + 1) exit )) m)
          (ensures (dllist_cons_interp p entry len exit m;
                    let c = sel_of (vcell p entry) m              in
                    let entry' = (p.cell entry).get_ref c Forward in
                    let sl1 = sel_of (dllist p entry' len exit) m in
                    sel_of (dllist p entry (len + 1) exit) m == dll_cons #p #entry #entry' #len #exit c sl1))
