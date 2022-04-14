module Learn.Steel.ListP.Data

module L   = FStar.List.Pure
module US  = Learn.Steel.Util
module T   = FStar.Tactics
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Reference

open Learn.Steel.ListP.Param


let mlist_cons_sel (p : list_param) (entry : ref p.r) (len' : nat) (exit : ref p.r)
                   (sels : (c : t_of (vcell p entry)
                              & mlist_sel_t p ((p.cell entry).get_next c) len' exit))
  : GTot (mlist_sel_t p entry (len'+1) exit)
  = let (|c, rs|) = sels in (|entry, (p.cell entry).get_data c|) :: rs

let rec mlist0 (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Pure vprop (requires True) (ensures fun v -> t_of v == mlist_sel_t p entry len exit)
               (decreases %[len; 0])
  =
    if len = 0
    then vrewrite (US.pure (entry == exit)) #(mlist_sel_t p entry len exit) (fun _ -> [])
    else vrewrite (vcell p entry `vdep` mlist_cons_vp p entry (len-1) exit)
                  (mlist_cons_sel p entry (len-1) exit)

and mlist_cons_vp (p : list_param) (entry : ref p.r) (len' : nat) (exit : ref p.r) (c : t_of (vcell p entry))
  : Pure vprop (requires True) (ensures fun v -> t_of v == mlist_sel_t p ((p.cell entry).get_next c) len' exit)
               (decreases %[len'; 1])
  = mlist0 p ((p.cell entry).get_next c) len' exit



let mlist_def (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : squash (mlist0 p entry len exit ==
           (if len = 0
            then vrewrite (US.pure (entry == exit)) #(mlist_sel_t p entry len exit) (fun _ -> [])
            else vrewrite (vcell p entry `vdep` mlist_cons_vp p entry (len-1) exit)
                          (mlist_cons_sel p entry (len-1) exit)))
  = _ by T.(compute (); trefl ())

let mlist_case_O (p : list_param) (entry : ref p.r) (exit : ref p.r)
  : Lemma (mlist0 p entry 0 exit ==
           vrewrite (US.pure (entry == exit)) #(mlist_sel_t p entry 0 exit) (fun _ -> []))
  = mlist_def p entry 0 exit

let mlist_case_S (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Lemma (mlist0 p entry (len+1) exit ==
           vrewrite (vcell p entry `vdep` mlist_cons_vp p entry len exit)
                    (mlist_cons_sel p entry len exit))
  = mlist_def p entry (len+1) exit

let mlist_sel_case_S (p : list_param) (r0 : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist0 p r0 (len+1) exit)) m)
          (ensures  Mem.interp (hp_of (vcell p r0)) m /\
                   (let c = sel_of (vcell p r0) m in
                    Mem.interp (hp_of (mlist_cons_vp p r0 len exit c)) m /\
                    sel_of (mlist0 p r0 (len+1) exit) m ==
                      mlist_cons_sel p r0 len exit (|c, sel_of (mlist_cons_vp p r0 len exit c) m|)))
  =
    mlist_case_S p r0 len exit;
    interp_vdep_hp (vcell p r0) (mlist_cons_vp p r0 len exit) m;
    calc (==) {
      sel_of (mlist0 p r0 (len+1) exit) m;
    == {}
      vrewrite_sel (vcell p r0 `vdep` mlist_cons_vp p r0 len exit)
                   (mlist_cons_sel p r0 len exit) m;
    == { vrewrite_sel_eq (vcell p r0 `vdep` mlist_cons_vp p r0 len exit)
                         (mlist_cons_sel p r0 len exit) m }
       mlist_cons_sel p r0 len exit
         (let (|c, rs|) =
           ((sel_of (vcell p r0 `vdep` mlist_cons_vp p r0 len exit) m)
            <: vdep_t (vcell p r0) (mlist_cons_vp p r0 len exit))
          in (|c, rs|));
    == { vdep_sel_eq (vcell p r0) (mlist_cons_vp p r0 len exit) m }
     (let c = sel_of (vcell p r0) m in
      mlist_cons_sel p r0 len exit
         (|c, sel_of (mlist_cons_vp p r0 len exit c) m|));
    }

(* expand the vprop *)

let mlist_sl (p : list_param) entry len exit =
  let VUnit r = mlist0 p entry len exit in r.hp

let mlist_sel (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) =
  let VUnit r = mlist0 p entry len exit in r.sel

let mlist_eq0 (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Lemma (mlist p entry len exit == mlist0 p entry len exit)
          [SMTPat (mlist p entry len exit)]
  = let VUnit _ = mlist0 p entry len exit in ()

(* intro/elim lemmas *)
(* Here those lemmas are typed with mlist0, but in the interface, we expose mlist (which is equal) *)

let intro_mlist_nil_lem (p : list_param) (r0 : ref p.r) (m : Mem.mem)
  : Lemma (ensures Mem.interp (hp_of (mlist0 p r0 0 r0)) m /\
                   sel_of (mlist0 p r0 0 r0) m == [])
  =
    mlist_case_O p r0 r0;
    US.intro_pure_lem (r0 == r0) m

let elim_mlist_nil_lem (p : list_param) (r0 r1 : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist0 p r0 0 r1)) m)
          (ensures  r0 == r1)
  =
    mlist_case_O p r0 r1;
    US.elim_pure_lem (r0 == r1) m

let intro_mlist_cons_lem (p : list_param) (r0 r1 : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : Lemma (requires Mem.interp (hp_of (vcell p r0 `star` mlist0 p r1 len exit)) m /\
                    (p.cell r0).get_next (sel_of (vcell p r0) m) == r1)
          (ensures  Mem.interp (hp_of (mlist0 p r0 (len+1) exit)) m /\
                    sel_of (mlist0 p r0 (len+1) exit) m ==
                      (|r0, (p.cell r0).get_data (sel_of (vcell p r0) m)|)
                      :: (sel_of (mlist0 p r1 len exit) m <: mlist_sel_t p r1 len exit))
  =
    mlist_case_S p r0 len exit;
    interp_vdep_hp (vcell p r0) (mlist_cons_vp p r0 len exit) m;
    mlist_sel_case_S p r0 len exit m

let elim_mlist_cons_lem (p : list_param) (r0 : ref p.r)
                        (hd : cell_t p) (tl : list (cell_t p))
                        (len : nat) (exit : ref p.r) (m: Mem.mem)
  : Lemma (requires Mem.interp (hp_of (mlist0 p r0 (len + 1) exit)) m /\
                    (sel_of (mlist0 p r0 (len + 1) exit) m
                      <: mlist_sel_t p r0 (len+1) exit) == hd :: tl)
          (ensures (let r1 = sg_entry tl exit in
                    Mem.interp (hp_of (vcell p r0 `star` mlist p r1 len exit)) m /\
                   (let c0 = sel_of (vcell p r0) m in
                    (p.cell r0).get_next c0 == r1 /\
                    (p.cell r0).get_data c0 == hd._2 /\
                    sel_of (mlist0 p r1 len exit) m == tl)))
  =
    mlist_case_S p r0 len exit;
    interp_vdep_hp (vcell p r0) (mlist_cons_vp p r0 len exit) m;
    mlist_sel_case_S p r0 len exit m
