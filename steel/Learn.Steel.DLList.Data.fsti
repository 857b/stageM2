module Learn.Steel.DLList.Data

module U   = Learn.Util
module L   = FStar.List.Pure
module Mem = Steel.Memory

open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.DLList.Param


#set-options "--fuel 1 --ifuel 1"

let sg_entry (#r : Type) (#a : r -> Type) (l : list (x:r & a x)) (nxt : r) : r =
  match l with
  | [] -> nxt
  | hd :: _ -> hd._1

let sg_exit  (#r : Type) (#a : r -> Type) (prv : r) (l : list (x:r & a x)) : r =
  if Cons? l then (L.last l)._1 else prv

noeq
type dllist_sel_t (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) : Type = {
  dll_sg  : L.llist (cell_t p) len;
  dll_prv : prv : ref p.r { exit  == sg_exit  prv dll_sg };
  dll_nxt : nxt : ref p.r { entry == sg_entry dll_sg nxt };
}

let dllist_sel_t_get_ref
      (#p : list_param) (#entry : ref p.r) (#len : nat) (#exit : ref p.r)
      (sl : dllist_sel_t p entry len exit)
  : Lemma (exit  == sg_exit  sl.dll_prv sl.dll_sg /\
           entry == sg_entry sl.dll_sg  sl.dll_nxt)
  = ()

let cons_sel (p : list_param) (entry : ref p.r) (len' : nat) (exit : ref p.r)
             (c : t_of (vcell p entry))
             (sl1 : dllist_sel_t p ((p.cell entry).get_ref c Forward) len' exit {sl1.dll_prv == entry})
  : GTot (dllist_sel_t p entry (len' + 1) exit)
  =
    let hd  = (|entry, (p.cell entry).get_data c|)  in
    let dll_sg  = hd :: sl1.dll_sg                    in
    let dll_prv = (p.cell entry).get_ref c Backward in
    U.assert_by (exit == sg_exit dll_prv dll_sg) (fun () ->
      dllist_sel_t_get_ref sl1;
      match sl1.dll_sg with
      | []    -> assert_norm (sg_exit dll_prv dll_sg == entry)
      | _ :: _ -> assert_norm (sg_exit dll_prv dll_sg == sg_exit sl1.dll_prv sl1.dll_sg)
    );
    {
      dll_sg; dll_prv;
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
           (sel_of (dllist p entry 0 exit) m <: dllist_sel_t p entry 0 exit) == {
              dll_sg  = [];
              dll_prv = exit;
              dll_nxt = entry;
            })

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
                    sel_of (dllist p entry (len + 1) exit) m
                      == cons_sel p entry len exit c sl1))
