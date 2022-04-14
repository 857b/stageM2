module Learn.Steel.ListP.Derived

module L  = FStar.List.Pure

(* [mlistN] *)

let v (p : list_param) (entry : ref p.r) (len : nat)
  = mlist p entry len null

let f (p : list_param) (entry : ref p.r) (len : nat) (l : t_of (v p entry len)) : mlistN_sel_t p entry
  = l

let mlistN_sl (p : list_param) (entry : ref p.r) =
  US.vexists_sl (v p entry)

let mlistN_indep (p : list_param) (entry : ref p.r)
  : Lemma (ensures US.vexists_indep (v p entry) (f p entry))
  = US.vexists_indepI_unique (v p entry) (mlistN_length_unique p entry)

let mlistN_sel (p : list_param) (entry : ref p.r) =
  mlistN_indep p entry;
  US.vexists_sel (v p entry) (f p entry)

let intro_mlistN #opened (p : list_param) entry len =
  mlistN_indep p entry;
  US.intro_vexists len (v p entry) (f p entry)

let elim_mlistN #opened (p : list_param) entry
  =
    mlistN_indep p entry;
    US.witness_vexists (v p entry) (f p entry)


(* append *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1" (* LONG *)
let rec intro_mlist_append #opened p r0 (len0 : nat) r1 (len1 : nat) r2
  =
    let h0 = get () in
    if len0 = 0
    then begin
        mlist_rew_len p r0 len0 0 r1;
      elim_mlist_nil p r0 r1;
      change_equal_slprop (mlist p r1 len1 r2) (mlist p r0 (len0+len1) r2);
      let h1 = get () in
      calc (==) {
        sel_list p r0 (len0+len1) r2 h1
          <: list (cell_t p);
      == {}
        sel_list p r1 len1 r2 h0;
      == {}
        L.(sel_list p r0 len0 r1 h0 @ sel_list p r1 len1 r2 h0);
      }
    end else begin
      let len0' = len0 - 1 in
        mlist_rew_len p r0 len0 (len0'+1) r1;
      let r0' = elim_mlist_cons p r0 len0' r1 in
      intro_mlist_append p r0' len0' r1 len1 r2;
      intro_mlist_cons   p r0 r0' (len0'+len1) r2;
        mlist_rew_len p r0 ((len0'+len1)+1) (len0+len1) r2;
      let h1 = get () in
      assert (sel_list p r0 (len0+len1) r2 h1 == L.(sel_list p r0 len0 r1 h0 @ sel_list p r1 len1 r2 h0))
    end

let rec elim_mlist_append #opened (p : list_param) r0 (len len0 len1 : nat) r2 (l0 l1 : list (cell_t p))
  =
    let h0 = get () in
    calc (==) {
      len;
    == {}
      L.length (sel_list p r0 len r2 h0);
    == {}
      L.(length (l0@l1));
    == {}
      len0 + len1;
    };
    if len0 = 0
    then begin
      intro_mlist_nil p r0;
        mlist_rew_len p r0 0 len0 r0;
        mlist_rew_len p r0 len len1 r2;
      r0
    end else begin
      let hd0 :: tl0 = l0 in
      let len'  = len  - 1 in
      let len0' = len0 - 1 in
        mlist_rew_len p r0 len (len'+1) r2;
      let r0' = elim_mlist_cons p r0 len' r2 in
      let r1  = elim_mlist_append p r0' len' len0' len1 r2 tl0 l1 in
      intro_mlist_cons p r0 r0' len0' r1;
        mlist_rew_len p r0 (len0'+1) len0 r1;
      r1
    end
#pop-options


(** applying ghost operations on the cells *)

let mlist_extract_case_0 #opened (p : list_param) entry len exit (i : nat)
  : SteelGhost (mlist_extract_rt p entry len exit i) opened
      (mlist p entry len exit) (fun rt -> vcell p rt.r `star` rt.c_vp)
      (requires fun h0 -> i = 0 /\ i < L.length (sel_list p entry len exit h0))
      (ensures  mlist_extract_ens p entry len exit i)
  =
    let sl = gget (mlist p entry len exit) in
    let len' = len - 1 in
    mlist_rew_len p entry len (len'+1) exit;
    let r1 = elim_mlist_cons p entry len' exit in (* TODO?: factorize with case_S *)
    let c_sl = gget (mlist p r1 len' exit) in
    let rt = {
      r = entry;
      c_vp = mlist p r1 len' exit;
      c_sl; nxt = r1; sl;
      close = (fun () ->
        intro_mlist_cons p entry r1 len' exit;
        mlist_rew_len p entry (len'+1) len exit)
    } in
    change_equal_slprop (vcell p entry `star` mlist p r1 len' exit)
                        (vcell p rt.r `star` rt.c_vp);
    rt

#push-options "--z3rlimit 15"
let rec mlist_extract_case_S #opened (p : list_param) entry len exit (i : nat)
  : SteelGhost (mlist_extract_rt p entry len exit i) opened
      (mlist p entry len exit) (fun rt -> vcell p rt.r `star` rt.c_vp)
      (requires fun h0 -> i > 0 /\ i < L.length (sel_list p entry len exit h0))
      (ensures  mlist_extract_ens p entry len exit i)
      (decreases %[i; 0])
  =
    let sl = gget (mlist p entry len exit) in
    let len' = len - 1 in
    mlist_rew_len p entry len (len'+1) exit;
    let r1 = elim_mlist_cons p entry len' exit in
    let c0_sl = gget (vcell p entry) in
    let rt' = mlist_extract p r1 len' exit (i-1) in
    let rt  = {rt' with
      c_vp = vcell p entry `star` rt'.c_vp;
      c_sl = (G.reveal c0_sl, rt'.c_sl); sl;
      close = (fun () ->
        rt'.close ();
        intro_mlist_cons p entry r1 len' exit;
        mlist_rew_len p entry (len'+1) len exit)
    } in
    change_equal_slprop (vcell p rt'.r `star` (vcell p entry `star` rt'.c_vp))
                        (vcell p rt.r  `star` rt.c_vp);
    rt

and mlist_extract #opened (p : list_param) entry len exit (i : nat)
  : SteelGhost (G.erased (mlist_extract_rt p entry len exit i)) opened
      (mlist p entry len exit) (fun rt -> vcell p rt.r `star` rt.c_vp)
      (requires fun h0 -> i < L.length (sel_list p entry len exit h0))
      (ensures  fun h0 rt h1 -> mlist_extract_ens p entry len exit i h0 rt h1)
      (decreases %[i; 1])
  = if i = 0 
    then let rt = mlist_extract_case_0 p entry len exit i in G.hide rt
    else let rt = mlist_extract_case_S p entry len exit i in G.hide rt
#pop-options
