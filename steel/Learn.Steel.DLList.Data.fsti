module Learn.Steel.DLList.Data

module U   = Learn.Util
module Mem = Steel.Memory

open FStar.List.Pure
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.DLList.Param


#set-options "--fuel 1 --ifuel 1"

let sg_hd (#p : list_param) (l : list (rcell_t p)) (nxt : ref p.r) : ref p.r =
  match l with
  | [] -> nxt
  | hd :: _ -> hd._1

let sg_lt  (#p : list_param) (prv : ref p.r) (l : list (rcell_t p)) : ref p.r =
  if Cons? l then (last l)._1 else prv

// ALT: dllist_sel_t' + refinement
// ALT: indexed by prv + entry ?
noeq
type dllist_sel_t (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r) : Type = {
  dll_sg  : llist (rcell_t p) len;
  dll_prv : prv : ref p.r { lt == sg_lt prv dll_sg };
  dll_nxt : nxt : ref p.r { hd == sg_hd dll_sg nxt };
}

let dllist_sel_t_get_ref
      (#p : list_param) (#hd : ref p.r) (#len : nat) (#lt : ref p.r)
      (sl : dllist_sel_t p hd len lt)
  : Lemma (lt == sg_lt sl.dll_prv sl.dll_sg /\
           hd == sg_hd sl.dll_sg  sl.dll_nxt)
  = ()

let dll_nil (#p : list_param) (hd : ref p.r) (lt : ref p.r)
  : dllist_sel_t p hd 0 lt
  = {
    dll_sg  = [];
    dll_prv = lt;
    dll_nxt = hd;
  }

/// [r1] should be [c.cl_nxt]
let dll_cons
      (#p : list_param) (#r0 #r1 : ref p.r) (#len' : nat) (#r2 : ref p.r)
      (c : cell_t p r0)
      (sl1 : dllist_sel_t p r1 len' r2 {sl1.dll_prv == r0})
  : GTot (dllist_sel_t p r0 (len' + 1) r2)
  = {
    dll_sg  = (|r0, c.cl_data|) :: sl1.dll_sg;
    dll_prv = c.cl_prv;
    dll_nxt = sl1.dll_nxt;
  }


val dllist_sl (p : list_param u#0) (hd : ref p.r) (len : nat) (lt : ref p.r)
  : Mem.slprop u#1

val dllist_sel (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r)
  : selector (dllist_sel_t p hd len lt) (dllist_sl p hd len lt)

[@@__steel_reduce__]
let dllist' (p : list_param) (hd : ref p.r) ([@@@smt_fallback] len : nat) (lt : ref p.r) : vprop' =
  {
    hp  = dllist_sl    p hd len lt;
    t   = dllist_sel_t p hd len lt;
    sel = dllist_sel   p hd len lt
  }
unfold let dllist (p : list_param) (hd : ref p.r) ([@@@smt_fallback] len : nat) (lt : ref p.r) : vprop =
  VUnit (dllist' p hd len lt)

[@@ __steel_reduce__]
let sel_dllist (#q:vprop) (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (dllist p hd len lt) /\ True)})
  : GTot (dllist_sel_t p hd len lt)
  = h (dllist p hd len lt)


val dllist_nil_interp (p : list_param) (hd : ref p.r) (lt : ref p.r) (m : Mem.mem)
  : Lemma (Mem.interp (hp_of (dllist p hd 0 lt)) m /\
           (sel_of (dllist p hd 0 lt) m <: dllist_sel_t p hd 0 lt) == dll_nil hd lt)

val dllist_cons_interp (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r) (m : Mem.mem)
  : Lemma (Mem.interp (hp_of (dllist p hd (len + 1) lt)) m
         <==> Mem.interp (hp_of (vcell p hd)) m /\
           (let c   = (p.cell hd).cl_f (sel_of (vcell p hd) m) in
            let hd' = c.cl_nxt                                 in
            Mem.interp (hp_of (vcell p hd) `Mem.star` hp_of (dllist p hd' len lt)) m /\
           (let sl1 : dllist_sel_t p hd' len lt
                    = sel_of (dllist p hd' len lt) m           in
            sl1.dll_prv == hd)))

val dllist_cons_sel_eq
      (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (dllist p hd (len + 1) lt )) m)
          (ensures (dllist_cons_interp p hd len lt m;
                    let c   = (p.cell hd).cl_f (sel_of (vcell p hd) m) in
                    let hd' = c.cl_nxt                                 in
                    let sl1 = sel_of (dllist p hd' len lt) m           in
                    sel_of (dllist p hd (len + 1) lt) m == dll_cons #p #hd #hd' #len #lt c sl1))
