module Learn.Steel.DLList.Data

module U   = Learn.Util
module T   = FStar.Tactics
module L   = FStar.List.Pure
module TL  = Learn.Tactics.Logic
module US  = Learn.Steel.Util
module Mem = Steel.Memory

#set-options "--fuel 1 --ifuel 1"


(**** Definition of the vprop *)

let rec dllist0 (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Pure vprop (requires True) (ensures fun v -> t_of v == dllist_sel_t p entry len exit)
               (decreases len)
  =
    if len = 0
    then
      vrewrite emp #(dllist_sel_t p entry len exit)
        (fun _ -> {
            dll_sg  = [];
            dll_prv = exit;
            dll_nxt = entry;
        })
    else
      let len' = len - 1 in
      vrewrite (vcell p entry `vdep` (fun c ->
          let entry' = (p.cell entry).get_ref c Forward in
          dllist0 p entry' len' exit `vrefine` (fun sl1 ->
            let sl1 : dllist_sel_t p entry' len' exit = U.cast _ sl1 in
            sl1.dll_prv == entry)))
        #(dllist_sel_t p entry len exit) (fun (|c, sl1|) -> cons_sel p entry len' exit c sl1)


(**** Expansion the vprop *)

let dllist_sl (p : list_param) entry len exit =
  let VUnit r = dllist0 p entry len exit in r.hp

let dllist_sel (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) =
  let VUnit r = dllist0 p entry len exit in r.sel

let dllist_eq0 (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r)
  : Lemma (dllist p entry len exit == dllist0 p entry len exit)
          [SMTPat (dllist p entry len exit)]
  = let VUnit _ = dllist0 p entry len exit in ()


(**** Intro/Elim lemmas *)

let dllist_nil_interp (p : list_param) (entry : ref p.r) (exit : ref p.r) (m : Mem.mem)
  : squash (Mem.interp (hp_of (dllist0 p entry 0 exit)) m /\
            sel_of (dllist0 p entry 0 exit) m == {
              dll_sg  = [];
              dll_prv = exit;
              dll_nxt = entry;
            })
  =
    let g0 : squash (Mem.interp (hp_of emp) m)
      = reveal_emp ();
        Mem.intro_emp m
    in
    _ by T.(
      norm [delta_only [`%dllist0]; zeta]; norm [iota; primops];
      split ();
        (norm [delta_only [`%hp_of]; zeta];
        norm [delta_only [`%vrewrite; `%vrewrite'; `%Mkvprop'?.hp]; iota];
        exact (``@g0));
        (norm [delta_only [`%sel_of]; zeta];
        norm [delta_only [`%vrewrite; `%vrewrite'; `%Mkvprop'?.sel]; iota];
        apply_lemma (`vrewrite_sel_eq))
  )

// TODO:MOVE
let rec process_hyps (ts : list (T.term -> T.Tac (list T.term))) (hs : list T.term) : T.Tac (list T.term)
  = T.(match hs with
    | [] -> []
    | h0 :: hs -> try first (map (fun (t : term -> Tac (list term)) () ->
                               let hs0 = t h0 in process_hyps ts L.(hs0 @ hs)) ts)
                with | _ -> h0 :: process_hyps ts hs
  )


let interp_star' (p q: Mem.slprop) (m: Mem.mem)
  : Lemma Mem.(interp (p `star` q) m <==>
      (exists (mp: mem) (mq: mem) . (disjoint mp mq /\ join mp mq == m) /\ (interp p mp /\ interp q mq)))
  = Mem.interp_star p q m

let sel_disj_eq_r (m m0 m1 : Mem.mem) (h_m : squash (Mem.disjoint m0 m1 /\ Mem.join m0 m1 == m))
                  (#a : Type) (hp : Mem.slprop) (s : selector a hp)
  : Lemma (requires Mem.interp hp m1)
          (ensures (Mem.join_commutative m0 m1; s m1 == s m))
  = Mem.join_commutative m0 m1

let dllist_cons_interp0 (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  : squash (Mem.interp (hp_of (dllist0 p entry (len + 1) exit)) m
         <==> Mem.interp (hp_of (vcell p entry)) m /\
           (let c = sel_of (vcell p entry) m in
            let entry' = (p.cell entry).get_ref c Forward in
            Mem.interp (hp_of (vcell p entry) `Mem.star` hp_of (dllist0 p entry' len exit)) m /\
           (let sl1 : dllist_sel_t p entry' len exit
                    = sel_of (dllist0 p entry' len exit) m in
            sl1.dll_prv == entry)))
  =
    let rew_len_neq_0 () : Lemma (len + 1 = 0 == false) = () in
    _ by T.(
      apply (`TL.rew_iff_left);
        norm [delta_only [`%dllist0]; zeta]; norm [iota];
        l_to_r [``@rew_len_neq_0];
        norm [delta_only [`%hp_of; `%vrewrite; `%vrewrite'; `%vdep; `%vdep'; `%Mkvprop'?.hp]; iota; zeta];
        apply_lemma (`interp_vdep_hp);
      apply (`TL.conj_morph_iff); apply (`TL.iff_refl);
      let _ = intro () in
      apply (`TL.rew_iff_left ); apply_lemma (`interp_star');
      apply (`TL.rew_iff_right); apply (`TL.conj_morph_iff);
        apply_lemma (`interp_star'); let _ = intro () in apply (`TL.iff_refl);
      apply (`TL.rew_iff_left);
        apply (`TL.exists_morph_iff); let _ = intro () in
        apply (`TL.exists_morph_iff); let _ = intro () in
        apply (`TL.conj_morph_iff); apply (`TL.iff_refl);
        let h_m = intro () in let h_m, _ = T.destruct_and h_m in
        let rew_sl = pose (`sel_disj_eq_r _ _ _ (Squash.return_squash (`#h_m))) in
        apply (`TL.conj_morph_iff); apply (`TL.iff_refl);
        let _ = intro () in
        apply (`TL.rew_iff_left);
          norm [delta_only [`%hp_of; `%Mkvprop'?.hp]; zeta; iota];
          apply_lemma (`interp_vrefine_hp);
        apply (`TL.conj_morph_iff); apply (`TL.iff_refl);
          let _ = intro () in
          l_to_r [binder_to_term rew_sl];
          apply (`TL.iff_refl); smt ();
      norm [delta_only [`%vcell]];
      smt ())

let dllist_cons_interp (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  = dllist_cons_interp0 p entry len exit m


unfold
let ref_hmem (m : Mem.mem) (v : vprop)
  : Pure (hmem v) (requires Mem.interp (hp_of v) m) (ensures fun m' -> m' == m)
  = m

let vrewrite_sel_eq'
      (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t)) (h: Mem.hmem (normal (hp_of v)))
      (sl0 : t_of v) (sl0_eq : squash (sel_of v h == sl0))
  : squash ((vrewrite_sel v f <: selector' _ _) h == f sl0)
  = vrewrite_sel_eq v f h

let vdep_sel_eq'
      (v: vprop) (p: ( (t_of v) -> Tot vprop)) (m: Mem.hmem (vdep_hp v p))
      (sl0 : t_of v) (sl0_eq : squash (Mem.interp (hp_of v) m) -> squash (sel_of v m == sl0))
      (sl1 : t_of (p sl0)) (sl1_eq : squash (Mem.interp (hp_of (p sl0)) m) -> squash (sel_of (p sl0) m == sl1))
  : squash (vdep_sel v p m == (|sl0, sl1|))
  =
    interp_vdep_hp v p m;
    sl0_eq ();
    sl1_eq ();
    vdep_sel_eq v p m

let vrefine_sel_eq'_aux
      (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: Mem.hmem (vrefine_hp v p))
      (sl0 : t_of v) (sl0_eq : squash (Mem.interp (hp_of v) m) -> squash (sel_of v m == sl0))
  : Lemma (p sl0)
  = vrefine_sel_eq v p m;
    sl0_eq ()

let vrefine_t_eq_ty
      (v: vprop) (p: (normal (t_of v) -> Tot prop))
      (sl0 sl1 : vrefine_t v p)
      (_ : squash (eq2 #(t_of v) sl0 sl1))
  : squash (eq2 #(vrefine_t v p) sl0 sl1)
  = ()

let vrefine_sel_eq'
      (v: vprop) (p: (normal (t_of v) -> Tot prop)) (m: Mem.hmem (vrefine_hp v p))
      (sl0 : t_of v) (sl0_eq : squash (Mem.interp (hp_of v) m) -> squash (sel_of v m == sl0))
  : squash (eq2 #(t_of v) (vrefine_sel v p m) sl0)
  =
    vrefine_sel_eq v p m;
    sl0_eq ()


let change_eq_type (#a #b : Type) (x y : a) (_ : squash (a == b)) (_ : squash (eq2 #b x y))
  : squash (eq2 #a x y)
  = ()

let dllist_cons_sel_eq0
      (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
      (_ : squash (Mem.interp (hp_of (dllist0 p entry (len + 1) exit )) m))
  : squash (dllist_cons_interp0 p entry len exit m;
            let c = sel_of (vcell p entry) (ref_hmem m (vcell p entry)) in
            let entry' = (p.cell entry).get_ref c Forward               in
            let sl1 = sel_of (dllist0 p entry' len exit) m              in
            sel_of (dllist0 p entry (len + 1) exit) m
              == cons_sel p entry len exit c sl1)
  =
    let _ = dllist_cons_interp0 p entry len exit m in
    let rew_len_neq_0 () : Lemma (len + 1 = 0 == false) = () in
    let rew_len_1     () : Lemma (len + 1 - 1 ==   len) = () in
    _ by T.(
      apply_lemma (`U.eq2_trans);
      norm [delta_only [`%dllist0]; zeta]; norm [iota];
      l_to_r [``@rew_len_neq_0];
      norm [delta_only [`%sel_of; `%Mkvprop'?.sel; `%vrewrite; `%vrewrite']; iota; zeta];
      apply (`vrewrite_sel_eq');
      norm [delta_only [`%sel_of; `%Mkvprop'?.sel; `%vdep; `%vdep']; iota; zeta];
      apply (`change_eq_type); later ();
      apply (`vdep_sel_eq');
      let _ = intro () in trefl ();
      let _ = intro () in
      norm [delta_only [`%sel_of; `%Mkvprop'?.sel; `%vrefine; `%vrefine']; iota; zeta];
      norm [delta_only [`%t_of]; zeta];
      norm [delta_only [`%Mkvprop'?.t]; iota];
      apply (`vrefine_t_eq_ty); apply (`change_eq_type); later ();
      apply (`vrefine_sel_eq');
      let _ = intro () in trefl ();

      norm [iota]; l_to_r [``@rew_len_1]; trefl ();
      trefl ();
      trefl ())

let dllist_cons_sel_eq
      (p : list_param) (entry : ref p.r) (len : nat) (exit : ref p.r) (m : Mem.mem)
  = 
    dllist_cons_interp p entry len exit m;
    dllist_cons_sel_eq0 p entry len exit m ()
