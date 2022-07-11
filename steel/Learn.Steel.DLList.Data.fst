module Learn.Steel.DLList.Data

module U   = Learn.Util
module T   = FStar.Tactics
module TL  = Learn.Tactics.Logic
module US  = Learn.Steel.Util
module TP  = Learn.Steel.TProp
module Mem = Steel.Memory

#set-options "--fuel 1 --ifuel 1"


(**** Definition of the vprop *)

let rec dllist_tp (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Tot (TP.tprop (dllist_sel_t p entry len exit)) (decreases len)
  = TP.(
    if len = 0
    then return (dll_nil entry exit)
    else begin
      let len' = len - 1 in
      c   <-- vprt (t_of (vcell p entry)) (vcell p entry); 
      let entry' = (p.cell entry).get_ref c Forward in
      sl1 <-- tpr (dllist_tp p entry' len' exit);
      _   <-- tpure (sl1.dll_prv == entry);
      return #(dllist_sel_t p entry len exit)
             (dll_cons #p #entry #((p.cell entry).get_ref c Forward) #len' #exit c sl1)
    end
  )

let dllist_sl (p : list_param) entry len exit =
  (dllist_tp p entry len exit).t_hp

let dllist_sel (p : list_param) entry len exit =
  (dllist_tp p entry len exit).t_sel


(**** Intro/Elim lemmas *)

let rew () = T.norm [delta_only [`%dllist_tp]; zeta]

let dllist_nil_interp (p : list_param) (entry : ref p.r) (exit : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p entry 0 exit in
    assert (Mem.interp (hp_of (dllist p entry 0 exit)) m /\
            sel_of (dllist p entry 0 exit) m == dll_nil entry exit)
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [1] in smt ())

let dllist_cons_interp (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p entry (len + 1) exit in
    assert (Mem.interp (hp_of (dllist p entry (len + 1) exit)) m
         <==> Mem.interp (hp_of (vcell p entry)) m /\
           (let c = sel_of (vcell p entry) m              in
            let entry' = (p.cell entry).get_ref c Forward in
            Mem.interp (hp_of (vcell p entry) `Mem.star` hp_of (dllist p entry' len exit)) m /\
           (let sl1 : dllist_sel_t p entry' len exit
                    = sel_of (dllist p entry' len exit) m in
            sl1.dll_prv == entry)))
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())

let dllist_cons_sel_eq
      (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  =
    let tp = dllist_tp p entry (len + 1) exit in
    dllist_cons_interp p entry len exit m;
    assert (let c      = sel_of (vcell p entry) m            in
            let entry' = (p.cell entry).get_ref c Forward    in
            let sl1    = sel_of (dllist p entry' len exit) m in
            sel_of (dllist p entry (len + 1) exit) m
              == dll_cons #p #entry #entry' #len #exit c sl1)
      by T.(let _ = TP.pose_interp_lemma (`(`@tp)) (``@m) rew [2] in smt ())
