module Learn.Steel.DLList.Data

module U   = Learn.Util
module T   = FStar.Tactics
module TL  = Learn.Tactics.Logic
module US  = Learn.Steel.Util
module TP  = Learn.Steel.TProp
module Mem = Steel.Memory

#set-options "--fuel 1 --ifuel 1"


(**** Definition of the vprop *)

let rec dllist_tp (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r)
  : Tot (TP.tprop (dllist_sel_t p hd len lt)) (decreases len)
  = TP.(
    if len = 0
    then return (dll_nil hd lt)
    else begin
      let len' = len - 1            in
      c   <-- vprt (t_of (vcell p hd)) (vcell p hd); 
      let c    = (p.cell hd).cl_f c in
      let hd'  = c.cl_nxt           in
      sl1 <-- tpr (dllist_tp p hd' len' lt);
      _   <-- tpure (sl1.dll_prv == hd);
      return #(dllist_sel_t p hd len lt) (dll_cons #p #hd #hd' #len' #lt c sl1)
    end
  )

let dllist_sl (p : list_param) hd len lt =
  (dllist_tp p hd len lt).t_hp

let dllist_sel (p : list_param) hd len lt =
  (dllist_tp p hd len lt).t_sel


(**** Intro/Elim lemmas *)

let rew () = T.norm [delta_only [`%dllist_tp]; zeta]

let dllist_nil_interp (p : list_param) (hd : ref p.r) (lt : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p hd 0 lt in
    assert (Mem.interp (hp_of (dllist p hd 0 lt)) m /\
            sel_of (dllist p hd 0 lt) m == dll_nil hd lt)
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [1] in smt ())

let dllist_cons_interp (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p hd (len + 1) lt in
    assert (Mem.interp (hp_of (dllist p hd (len + 1) lt)) m
         <==> Mem.interp (hp_of (vcell p hd)) m /\
           (let c   = (p.cell hd).cl_f (sel_of (vcell p hd) m) in
            let hd' = c.cl_nxt                                 in
            Mem.interp (hp_of (vcell p hd) `Mem.star` hp_of (dllist p hd' len lt)) m /\
           (let sl1 : dllist_sel_t p hd' len lt
                    = sel_of (dllist p hd' len lt) m           in
            sl1.dll_prv == hd)))
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())

let dllist_cons_sel_eq
      (p : list_param) (hd : ref p.r) (len : nat) (lt : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p hd (len + 1) lt in
    dllist_cons_interp p hd len lt m;
    assert (dllist_cons_interp p hd len lt m;
            let c   = (p.cell hd).cl_f (sel_of (vcell p hd) m) in
            let hd' = c.cl_nxt                                 in
            let sl1 = sel_of (dllist p hd' len lt) m           in
            sel_of (dllist p hd (len + 1) lt) m == dll_cons #p #hd #hd' #len #lt c sl1)
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())
