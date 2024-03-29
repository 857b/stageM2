module Experiment.Steel.Repr.LV

module L    = FStar.List.Pure
module Perm = Learn.Permutation

open FStar.List.Pure
open Learn.List.Mask
open FStar.Tactics


let eij_equiv_injective (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (Perm.injective (eij_equiv_f eij))
  =
    Perm.injectiveI (eij_equiv_f eij) (fun i i' ->
      let k  = L.index eij i    in
      let k' = L.index eij i'   in
      let m  = eij_trg_mask eij in
      L.lemma_index_memP eij i;
      L.lemma_index_memP eij i';
      assert (mask_pull m (mask_push m k) == mask_pull m (mask_push m k')))

let eij_equiv_surjective (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (Perm.surjective (eij_equiv_f eij))
  =
    Perm.surjectiveI (eij_equiv_f eij) (fun j ->
      let k = mask_pull (eij_trg_mask eij) j in
      Ll.mem_findi k eij)

#push-options "--ifuel 0 --fuel 0"
let eij_equiv_eq (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg) (i : Fin.fin (L.length src))
  : Lemma (L.index src i == L.index (filter_mask (eij_trg_mask eij) trg) (eij_equiv_f eij i))
  = L.lemma_index_memP eij i
#pop-options

let eij_trg_mask_len (#a : Type) (#src #trg : list a) (eij : eq_injection_l src trg)
  : Lemma (mask_len (eij_trg_mask eij) == L.length src)
  =
    eij_equiv_injective eij;
    Perm.fin_injective_le (L.length src) (mask_len (eij_trg_mask eij)) (eij_equiv_f eij);
    eij_equiv_surjective eij;
    Perm.fin_surjective_ge (L.length src) (mask_len (eij_trg_mask eij)) (eij_equiv_f eij)

#push-options "--ifuel 0 --fuel 0"
let extract_eij_equiv
      (#src #trg : vprop_list) (eij : eq_injection_l src trg) (sl : sl_f trg)
  : Lemma (extract_vars (eij_equiv eij) (filter_sl (eij_trg_mask eij) sl) == eij_sl (L.index eij) sl)
  = Fl.flist_extensionality
      (extract_vars (eij_equiv eij) (filter_sl (eij_trg_mask eij) sl))
      (eij_sl (L.index eij) sl)
      (fun i ->
        let m = eij_trg_mask eij in
        L.lemma_index_memP eij i;
        assert (extract_vars (eij_equiv eij) (filter_sl (eij_trg_mask eij) sl) i
             == U.cast _ (sl (mask_pull m (mask_push m (L.index eij i)))))
            by (trefl ()))
#pop-options

let eij_split_assoc_left (s0 s1 s2 : vprop_list) (t : vprop_list) (f : eq_injection_l L.(s0 @ s1 @ s2) t)
  : Lemma (
      (**) L.append_assoc s0 s1 s2;
      (eij_split s0 s1 (eij_split L.(s0 @ s1) s2 f)._1)._1 == (eij_split s0 L.(s1 @ s2) f)._1)
  =
    L.append_assoc s0 s1 s2;
    let f0 = (eij_split L.(s0 @ s1) s2 f)._1 in
    Ll.list_extensionality (eij_split s0 s1 f0)._1 (eij_split s0 L.(s1 @ s2) f)._1
      (fun i -> Ll.splitAt_index L.(length (s0 @ s1)) f;
             Ll.splitAt_index L.(length s0) f0;
             Ll.splitAt_index L.(length s0) f)

#push-options "--ifuel 0 --fuel 0"
let eij_split1_trg_mask (#a : Type) (src0 src1 #trg : list a) (eij : eq_injection_l L.(src0 @ src1) trg)
  : Lemma (eij_trg_mask eij == mask_comp_or (eij_trg_mask (eij_split  src0 src1 eij)._1)
                                            (eij_trg_mask (eij_split1 src0 src1 eij)))
  =
    let n0     = L.length src0 in
    let n1     = L.length src1 in
    let r0, r1 = eij_split  src0 src1 eij   in
    let r1'    = eij_split1 src0 src1 eij   in
    let m      = mask_not (eij_trg_mask r0) in
    Ll.splitAt_index n0 eij;
    Ll.list_extensionality
      (eij_trg_mask eij) (mask_comp_or (eij_trg_mask r0) (eij_trg_mask r1'))
    L.(fun i ->
        calc (<==>) {
          b2t (index (eij_trg_mask eij) i);
        <==> { Ll.lemma_splitAt_append n0 eij }
          memP i (r0 @ r1);
        <==> { L.append_mem r0 r1 i }
          memP i r0 \/ memP i r1;
        <==> { introduce ~(memP i r0) ==> (memP i r1 <==> memP (mask_push m i) r1') with _ . (
             Ll.memP_iff i r1; Ll.memP_iff (mask_push m i) r1';
             introduce forall (j : Fin.fin n1) . index r1 j == i <==> index r1' j == mask_push m i
               with introduce _ /\ _ with ()
                and introduce _ ==> _ with _ . (
                    Ll.memP_iff (index r1 j) r0;
                    assert (index r1' j == mask_push m (index r1 j))
           )) }
          index (eij_trg_mask r0) i \/ index (eij_trg_mask r1') (mask_push m i);
        <==> { }
          L.index (mask_comp_or (eij_trg_mask r0) (eij_trg_mask r1')) i;
        }
      )
#pop-options


let bind_g_csm'_len
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
  : Lemma (mask_len (bind_g_csm' f_prd g_csm) == L.length f_prd + mask_len g_csm)
          [SMTPat (mask_len (bind_g_csm' f_prd g_csm))]
  =
    append_count (Ll.repeat (length f_prd) true) g_csm true;
    Ll.repeat_count (length f_prd) true true

#push-options "--ifuel 0"
let rec bind_g_csm'_or_aux
      (n m : nat) (f : Ll.vec m bool) (g : Ll.vec (mask_len (mask_not f)) bool)
  : Lemma (ensures  (append_count (Ll.repeat n true) f true; Ll.repeat_count n true true;
                     mask_comp_or #(n+m) (Ll.repeat n true @ f) g == Ll.repeat n true @ mask_comp_or f g))
          (decreases n)
  = if n > 0 then begin
      append_count (Ll.repeat   n   true) f true; Ll.repeat_count   n   true true;
      bind_g_csm'_or_aux (n-1) m f g
    end
#pop-options

let bind_g_csm'_or
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
      (csm1  : csm_t (filter_mask (mask_not g_csm) env))
  : Lemma (mask_comp_or (bind_g_csm' f_prd g_csm) csm1
        == bind_g_csm' f_prd (mask_comp_or g_csm csm1))
  =
    bind_g_csm'_or_aux (length f_prd) (length env) g_csm csm1

#push-options "--ifuel 0 --fuel 0"

let filter_bind_csm
      (env : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (filter_mask (mask_not (bind_csm env f_csm g_csm)) env
        == filter_mask (mask_not g_csm) (filter_mask (mask_not f_csm) env))
  =
    mask_not_comp_or f_csm g_csm;
    filter_mask_and (mask_not f_csm) (mask_not g_csm) env

let filter_sl_bind_csm
      (env : vprop_list)
      (f_csm : csm_t env)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (sl : sl_f env)
  : Lemma (filter_bind_csm env f_csm g_csm;
       filter_sl (mask_not (bind_csm env f_csm g_csm)) sl
    == filter_sl (mask_not g_csm) (filter_sl (mask_not f_csm) sl))
  =
    mask_not_comp_or f_csm g_csm;
    filter_mask_fl_and (mask_not f_csm) (mask_not g_csm) (vprop_list_sels_t env) sl

#push-options "--fuel 1 --ifuel 1"
let rec bind_g_csm'_as_comp_or
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
  : Lemma (ensures bind_g_csm' f_prd g_csm
                == mask_comp_or (mask_split_l (L.length f_prd) (L.length env)) g_csm)
          (decreases f_prd)
  = match f_prd with
  | [] -> mask_comp_or_repeat_true (L.length env) g_csm
  | _ :: f_prd -> bind_g_csm'_as_comp_or f_prd g_csm
#pop-options

let filter_csm_bind_g_csm'
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
  : Lemma (filter_mask (bind_g_csm' f_prd g_csm) L.(f_prd @ env)
        == L.(f_prd @ filter_mask g_csm env))
  =
    filter_mask_append (Ll.repeat (L.length f_prd) true) g_csm f_prd env;
    filter_mask_true (Ll.repeat (L.length f_prd) true) f_prd (fun i -> ())

let filter_bind_g_csm'
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
  : Lemma (filter_mask (mask_not (bind_g_csm' f_prd g_csm)) L.(f_prd @ env)
        == filter_mask (mask_not g_csm) env)
  =
    let m1 : Ll.vec (length f_prd + L.length env) bool
      = Ll.repeat (length f_prd) true @ g_csm in
    let m2 : Ll.vec (length f_prd + L.length env) bool
      = Ll.repeat (length f_prd) false @ mask_not g_csm in
    calc (==) {
      filter_mask (mask_not (bind_g_csm' f_prd g_csm)) L.(f_prd @ env) <: vprop_list;
    == { }
      filter_mask (mask_not m1) (f_prd @ env);
    == { Ll.pat_append () }
      filter_mask m2 (f_prd @ env);
    == { filter_mask_append (Ll.repeat (length f_prd) false) (mask_not g_csm) f_prd env }
      filter_mask (Ll.repeat (length f_prd) false) f_prd @ filter_mask (mask_not g_csm) env;
    == { filter_mask_false (Ll.repeat (length f_prd) false) f_prd (fun _ -> ()) }
      [] @ filter_mask (mask_not g_csm) env;
    == { _ by (Tactics.trefl ()) }
      filter_mask (mask_not g_csm) env;
    == {  }
      filter_mask (mask_not g_csm) env;
    }

let filter_bind_g_csm'1
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (filter_mask (mask_not (bind_g_csm'1 env f_csm f_prd g_csm)) (res_env env f_csm f_prd)
        == filter_mask (mask_not (bind_csm env f_csm g_csm)) env)
  =
    filter_bind_g_csm' f_prd g_csm;
    filter_bind_csm env f_csm g_csm


let filter_sl_bind_g_csm'
      (f_prd : vprop_list) (#env : vprop_list) (g_csm : csm_t env)
      (sl0 : sl_f f_prd) (sl1 : sl_f env)
  : Lemma (filter_bind_g_csm' f_prd g_csm;
       filter_sl (mask_not (bind_g_csm' f_prd g_csm)) (append_vars sl0 sl1)
    == filter_sl (mask_not g_csm) sl1)
  =
    filter_bind_g_csm' f_prd g_csm;
    Ll.pat_append ();
    let m1 : Ll.vec (length f_prd + length env) bool
      = Ll.repeat (length f_prd) true @ g_csm in
    let m2 : Ll.vec (length f_prd + length env) bool
      = Ll.repeat (length f_prd) false @ mask_not g_csm in
    let rep0 = Ll.repeat (length f_prd) false in

    filter_mask_append rep0 (mask_not g_csm) f_prd env;
    filter_mask_false rep0 f_prd (fun _ -> ());
    assert_norm (vprop_list_sels_t [] == []);
    
    calc (==) {
      filter_sl (mask_not (bind_g_csm' f_prd g_csm)) (append_vars sl0 sl1);
    == { }
      filter_sl (mask_not m1) (append_vars sl0 sl1);
    == { }
      filter_sl m2 (append_vars sl0 sl1);
    == { filter_mask_fl_append rep0 (mask_not g_csm) _ _ sl0 sl1 }
      append_vars (filter_sl rep0 sl0) (filter_sl (mask_not g_csm) sl1);
    == { Fl.nil_uniq (filter_sl rep0 sl0) }
      append_vars #[] Fl.nil (filter_sl (mask_not g_csm) sl1);
    == { }
      filter_sl (mask_not g_csm) sl1;
    }

let gen_csm_pequiv_append (env : vprop_list) (csm : csm_t env)
  : Lemma (eij_trg_mask (eij_split (filter_mask csm env) (filter_mask (mask_not csm) env)
                                                 (Perm.perm_f_to_list (mask_pequiv_append csm env)))._1
           == csm)
  =
    let m0   = (filter_mask csm env)                            in
    let m1   = (filter_mask (mask_not csm) env)                 in
    let n0   = L.length m0                                      in
    let f    = Perm.perm_f_to_list (mask_pequiv_append csm env) in
    let f'   = (eij_split m0 m1 f)._1                           in
    let csm' = eij_trg_mask f'                                  in
    Ll.list_extensionality csm' csm
      (fun j ->
        calc (<==>) {
          b2t (L.index csm' j);
        <==> { Ll.memP_iff j f' }
          exists (i : Fin.fin n0) . L.index f' i == j;
        <==> { Ll.splitAt_index n0 f }
          exists (i : Fin.fin n0) . L.index f  i == j;
        <==> { FStar.Classical.forall_intro (mask_perm_append_index csm) }
          exists (i : Fin.fin n0) . mask_pull csm i == j;
        <==> { assert (L.index csm j ==> mask_pull csm (mask_push csm j) == j) }
          L.index csm j;
        }
      )

#pop-options

(**) private let __begin_lin_cond = ()


#set-options "--ifuel 0 --fuel 0"

let sub_ret_prd_f_eij
      (#env : vprop_list)
      (#prd0 : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1 : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
  : Lemma (is_eq_injection prd1 env (sub_ret_prd_f' csm_f0 prd_f1))
  =
    (**) Ll.pat_append ();
    let n0    = length prd0 in
    let ncsm0 = mask_not (eij_trg_mask csm_f0) in
    let f : Fin.fin (length prd1) -> _ = sub_ret_prd_f' csm_f0 prd_f1 in
    (**) assert (eq_injection_eq prd1 env f);
    Perm.injectiveI f (fun i i' ->
      let j  = f i       in
      let k  = prd_f1 i  in
      let k' = prd_f1 i' in

      U.assert_by (k == k') (fun () ->
        if k < n0 && k' < n0
        then assert (index csm_f0 k == index csm_f0 k') // then injectivity of csm_f0
        else if k >= n0 && k' >= n0
        then // by injectivity of mask_pull
          assert (
             mask_push csm1 (mask_push ncsm0 (mask_pull ncsm0 (mask_pull csm1 (k - n0))))
          ==
             mask_push csm1 (mask_push ncsm0 (mask_pull ncsm0 (mask_pull csm1 (k' - n0)))))
        else if k < n0 && k' >= n0
        then begin
          assert (index ncsm0 j);      // by k'
          assert (~(mem j csm_f0));    // definition of [eij_trg_mask]
          assert (j = index csm_f0 k); // since k < n0
          lemma_index_memP csm_f0 k;
          false_elim ()
        end else begin
          assert (k >= n0 && k' < n0);
          assert (~(mem j csm_f0));
          lemma_index_memP csm_f0 k';
          false_elim ()
        end);
      Perm.perm_f_injective prd_f1
    )

#push-options "--z3rlimit 20"
let sub_ret_prd_f_eij_trg_eq
      (#env : vprop_list)
      (#prd0 : vprop_list) (csm_f0 : eq_injection_l prd0 env)
      (#csm1 : csm_t (filter_mask (mask_not (eij_trg_mask csm_f0)) env)) (#prd1 : vprop_list)
      (prd_f1 : vequiv_perm (sub_prd env (eij_trg_mask csm_f0) prd0 csm1) prd1)
  : Lemma (bind_csm env (eij_trg_mask csm_f0) csm1 == eij_trg_mask (sub_ret_prd_f csm_f0 (prd_f1)))
  = Ll.list_extensionality
      (bind_csm env (eij_trg_mask csm_f0) csm1) (eij_trg_mask (sub_ret_prd_f csm_f0 (prd_f1)))
    (fun j ->
        let n0    = length prd0 in
        let csm0  = eij_trg_mask csm_f0 in
        let ncsm0 = mask_not csm0 in
        calc (==) {
          index (bind_csm env csm0 csm1) j;
        == { }
          index (mask_comp_or csm0 csm1) j;
        == { mask_comp_or_index csm0 csm1 j }
          index csm0 j || index csm1 (mask_push ncsm0 j);
        };
        calc (<==>) {
          b2t (index (eij_trg_mask (sub_ret_prd_f csm_f0 (prd_f1))) j);
        <==> { }
          memP j (sub_ret_prd_f csm_f0 (prd_f1));
        <==> { Ll.memP_iff j (sub_ret_prd_f csm_f0 (prd_f1)) }
          exists (i : Fin.fin (length prd1)) . index (sub_ret_prd_f csm_f0 (prd_f1)) i == j;
        <==> { }
          exists (i : Fin.fin (length prd1)) .
            (let k = prd_f1 i in
             if k < n0 then index csm_f0 k else (mask_pull ncsm0 (mask_pull csm1 (k - n0)))) == j;
        <==> { introduce forall (k : Fin.fin (length (sub_prd env csm0 prd0 csm1))) . exists (i : Fin.fin (length prd1)) .
                         k = prd_f1 i
               with assert Perm.(prd_f1 (inv_f prd_f1 k) == (prd_f1 `comp` inv_f prd_f1) k) }
          exists (k : Fin.fin (length (sub_prd env csm0 prd0 csm1))) .
            (if k < n0 then index csm_f0 k else (mask_pull ncsm0 (mask_pull csm1 (k - n0)))) == j;
        <==> { introduce forall (k' : Fin.fin (mask_len csm1)) .
                       exists (k : Fin.fin (length (sub_prd env csm0 prd0 csm1))) .
                         k' = k - n0
               with assert (k' = (k'+n0) - n0) }
             (exists (k : Fin.fin n0) . index csm_f0 k == j)
          \/ (exists (k : Fin.fin (mask_len csm1)) .
                (mask_pull ncsm0 (mask_pull csm1 k)) == j);
        <==> { Ll.memP_iff j csm_f0 }
          index csm0 j \/ (exists (k : Fin.fin (mask_len csm1)) . (mask_pull csm1 k == mask_push ncsm0 j));
        <==> { introduce forall (j' : Fin.fin (mask_len ncsm0)) .
                 (exists (k : Fin.fin (mask_len csm1)) . mask_pull csm1 k == j') <==> index csm1 j'
               with assert (index csm1 j' ==> (mask_pull csm1 (mask_push csm1 j')) == j') }
          index csm0 j \/ index csm1 (mask_push ncsm0 j);
        }
      )
#pop-options


#push-options "--ifuel 1 --fuel 0 --z3rlimit 20"
(**) private let ___begin_lc_sub_push = ()


let norm_lcsbl (norm_atlv : bool) : Tac unit =
      norm [delta_only [`%lc_sub_push; `%lc_sub_push_aux]; zeta]; norm [iota];
      norm [delta_only [`%lcsubp_LCret; `%lcsubp_LCbind; `%lcsubp_LCbindP; `%lcsubp_LCif; `%lcsubp_LCsub];
            iota; zeta];
      if norm_atlv then (norm [delta_only [`%lcsub_at_leaves]; zeta]; norm [iota])

let rew_lcsub_at_leaves_csm
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
      (csm' : csm_t env)
      (pf : squash (lcsub_at_leaves u#a u#p #env #a #t #csm #prd ct))
      (_ : squash (csm == csm'))
  : squash (lcsub_at_leaves #env #a #t #csm' #prd ct)
  = pf

// TODO? use t_destruct

#push-options "--ifuel 1 --fuel 1"
let rec lc_sub_push_at_leaves
      (env : vprop_list) (#a : Type) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond u#a u#p env t csm prd)
  : Lemma (ensures lcsub_at_leaves (lc_sub_push ct)) (decreases %[ct; 1])
  = match ct with
  | LCspec _ _ _ _ | LCret  _ _ _ | LCgen _ _ _ -> ()
  | LCbind env f_csm f_prd cf g_csm g_prd cg ->
      assert (lcsub_at_leaves (lc_sub_push (LCbind env f_csm f_prd cf g_csm g_prd cg)))
          by (norm_lcsbl true;
              split ();
                apply_lemma (``@lc_sub_push_at_leaves);
                let _ = forall_intro () in apply_lemma (``@lc_sub_push_at_leaves))
  | LCbindP env #a #b #wp #g csm0 prd0 cg ->
      assert (lcsub_at_leaves (lc_sub_push (LCbindP env #a #b #wp #g csm0 prd0 cg)))
          by (norm_lcsbl true;
              let _ = forall_intro () in apply_lemma (``@lc_sub_push_at_leaves))
  | LCif   env #a #guard #thn #els csm0 prd0 cthn cels ->
      assert (lcsub_at_leaves (lc_sub_push (LCif env #a #guard #thn #els csm0 prd0 cthn cels)))
          by (norm_lcsbl true;
              split ();
                apply_lemma (``@lc_sub_push_at_leaves);
                apply_lemma (``@lc_sub_push_at_leaves))
  | LCsub  env csm prd cf csm' prd' prd_f ->
      lc_sub_push_aux_at_leaves _ cf csm' prd' prd_f

and lc_sub_push_aux_at_leaves
      (env : vprop_list) (#a0 : Type) (#t0 : M.prog_tree a0) (#csm0 : csm_t env) (#prd0 : prd_t a0)
      (ct0 : lin_cond u#a u#p env t0 csm0 prd0)
      (csm'0 : csm_t (filter_mask (mask_not csm0) env)) (prd'0 : prd_t a0)
      (prd_f0 : ((x : a0) -> Perm.pequiv_list (sub_prd env csm0 (prd0 x) csm'0) (prd'0 x)))
  : Lemma (ensures lcsub_at_leaves (lc_sub_push_aux ct0 csm'0 prd'0 prd_f0)) (decreases %[ct0; 0])
  =
    let goal #a #t #csm #prd ct csm' prd' prd_f =
      lcsub_at_leaves (lc_sub_push_aux #env #a #t #csm #prd ct csm' prd' prd_f) in
    match_lin_cond ct0
      (fun a t csm prd ct ->
         (csm' : csm_t (filter_mask (mask_not csm) env)) -> (prd' : prd_t a) ->
         (prd_f : ((x : a) -> Perm.pequiv_list (sub_prd env csm (prd x) csm') (prd' x))) ->
         squash (goal ct csm' prd' prd_f))
    begin fun (*LCspec*) a sp s sh pre_f -> fun csm' prd' prd_f ->
      U.assert_by_tac (fun () -> norm_lcsbl true; trivial ())
    end
    begin fun (*LCret*)  a x sl_hint prd csm_f -> fun csm' prd' prd_f ->
      assert (goal (LCret env #a #x #sl_hint prd csm_f) csm' prd' prd_f)
          by (norm_lcsbl true; trivial ())
    end
    begin fun (*LCbind*) a b f g f_csm f_prd cf g_csm g_prd cg -> fun csm' prd' prd_f ->
      // Some guards generated by the tactic
      let gd0 : squash (L.length csm' =
                        L.length (filter_mask (mask_not g_csm) (filter_mask (mask_not f_csm) env)))
              = filter_bind_csm env f_csm g_csm in
      let gd1 (x : a) : squash (L.length csm' =
                        L.length (filter_mask (mask_not (bind_g_csm'1 env f_csm (f_prd x) g_csm))
                                              (res_env env f_csm (f_prd x))))
              = filter_bind_g_csm' (f_prd x) g_csm in
      FStar.Classical.forall_intro_squash_gtot gd1;
      assert (goal (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg) csm' prd' prd_f)
          by (norm_lcsbl true;
              split ();
                apply_lemma (`lc_sub_push_at_leaves);
                let _ = forall_intro () in
                  apply (`rew_lcsub_at_leaves_csm);
                  apply_lemma (`lc_sub_push_aux_at_leaves);
                  apply_lemma (`bind_g_csm'_or))
    end
    begin fun (*LCbindP*) a b wp g csm0 prd0 cg -> fun csm1 prd1 prd_f ->
      assert (goal (LCbindP env #a #b #wp #g csm0 prd0 cg) csm1 prd1 prd_f)
          by (norm_lcsbl true;
              let _ = forall_intro () in
              apply_lemma (`lc_sub_push_aux_at_leaves))
    end
    begin fun (*LCif*)   a guard thn els csm0 prd0 cthn cels -> fun csm1 prd1 prd_f ->
      U.assert_by_tac (fun () ->
              norm_lcsbl true;
              split ();
                apply_lemma (`lc_sub_push_aux_at_leaves);
                apply_lemma (`lc_sub_push_aux_at_leaves))
    end
    begin fun (*LCgen*)  a gen_tac gen_c c pre_f -> fun csm2 prd2 prd_f2 ->
      U.assert_by_tac (fun () ->
              norm_lcsbl true;
              trivial ())
    end
    begin fun (*LCsub*)  a f csm0 prd0 cf csm1 prd1 prd_f1 -> fun csm2 prd2 prd_f2 ->
      assert (goal (LCsub env #a #f csm0 prd0 cf csm1 prd1 prd_f1) csm2 prd2 prd_f2)
          by (norm_lcsbl false;
              apply (`rew_lcsub_at_leaves_csm);
              apply_lemma (`lc_sub_push_aux_at_leaves);
              smt ())
    end csm'0 prd'0 prd_f0
#pop-options
