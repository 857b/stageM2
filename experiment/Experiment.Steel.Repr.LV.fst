module Experiment.Steel.Repr.LV

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


let bind_g_csm'_len
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (mask_len (bind_g_csm' env f_csm f_prd g_csm) == length f_prd + mask_len g_csm)
          [SMTPat (mask_len (bind_g_csm' env f_csm f_prd g_csm))]
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
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (csm1  : csm_t (filter_mask (mask_not g_csm) (filter_mask (mask_not f_csm) env)))
  : Lemma (mask_comp_or (bind_g_csm' env f_csm f_prd g_csm) csm1
        == bind_g_csm' env f_csm f_prd (mask_comp_or g_csm csm1))
  =
    bind_g_csm'_or_aux (length f_prd) (mask_len (mask_not f_csm)) g_csm csm1

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


let filter_bind_g_csm'
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
  : Lemma (filter_mask (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (res_env env f_csm f_prd)
        == filter_mask (mask_not (bind_csm env f_csm g_csm)) env)
  =
    let env1 = filter_mask (mask_not f_csm) env in
    let m1 : Ll.vec (length f_prd + mask_len (mask_not f_csm)) bool
      = Ll.repeat (length f_prd) true @ g_csm in
    let m2 : Ll.vec (length f_prd + mask_len (mask_not f_csm)) bool
      = Ll.repeat (length f_prd) false @ mask_not g_csm in
    calc (==) {
      filter_mask (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (res_env env f_csm f_prd) <: vprop_list;
    == { }
      filter_mask (mask_not m1) (f_prd @ env1);
    == { Ll.pat_append () }
      filter_mask m2 (f_prd @ env1);
    == { filter_mask_append (Ll.repeat (length f_prd) false) (mask_not g_csm) f_prd env1 }
      filter_mask (Ll.repeat (length f_prd) false) f_prd @ filter_mask (mask_not g_csm) env1;
    == { filter_mask_false (Ll.repeat (length f_prd) false) f_prd (fun _ -> ()) }
      [] @ filter_mask (mask_not g_csm) env1;
    == { _ by (Tactics.trefl ()) }
      filter_mask (mask_not g_csm) env1;
    == { filter_bind_csm env f_csm g_csm }
      filter_mask (mask_not (bind_csm env f_csm g_csm)) env;
    }

let filter_sl_bind_g_csm'
      (env : vprop_list)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env))
      (sl0 : sl_f f_prd) (sl1 : sl_f (filter_mask (mask_not f_csm) env))
  : Lemma (filter_bind_g_csm' env f_csm f_prd g_csm; filter_bind_csm env f_csm g_csm;
       filter_sl (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (append_vars sl0 sl1)
    == filter_sl (mask_not g_csm) sl1)
  =
    filter_bind_g_csm' env f_csm f_prd g_csm; filter_bind_csm env f_csm g_csm;
    Ll.pat_append ();
    let env1 = filter_mask (mask_not f_csm) env in
    let m1 : Ll.vec (length f_prd + mask_len (mask_not f_csm)) bool
      = Ll.repeat (length f_prd) true @ g_csm in
    let m2 : Ll.vec (length f_prd + mask_len (mask_not f_csm)) bool
      = Ll.repeat (length f_prd) false @ mask_not g_csm in
    let rep0 = Ll.repeat (length f_prd) false in

    filter_mask_append rep0 (mask_not g_csm) f_prd env1;
    filter_mask_false rep0 f_prd (fun _ -> ());
    assert_norm (vprop_list_sels_t [] == []);
    
    calc (===) {
      filter_sl (mask_not (bind_g_csm' env f_csm f_prd g_csm)) (append_vars sl0 sl1);
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

#pop-options

(**) private let __end_bind_lem = ()

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
      norm [delta_only [`%lcsubp_LCret; `%lcsubp_LCbind; `%lcsubp_LCsub]; iota; zeta];
      if norm_atlv then (norm [delta_only [`%lcsub_at_leaves]; zeta]; norm [iota])

let rew_lcsub_at_leaves_csm
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
      (csm' : csm_t env)
      (pf : squash (lcsub_at_leaves #env #a #t #csm #prd ct))
      (_ : squash (csm == csm'))
  : squash (lcsub_at_leaves #env #a #t #csm' #prd ct)
  = pf

// TODO? use t_destruct

#push-options "--ifuel 1 --fuel 1"
let rec lc_sub_push_at_leaves
      (env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a) (#csm : csm_t env) (#prd : prd_t a)
      (ct : lin_cond env t csm prd)
  : Lemma (ensures lcsub_at_leaves (lc_sub_push ct)) (decreases %[ct; 1])
  = match ct with
  | LCspec _ _ _ _ | LCret  _ _ _ -> ()
  | LCbind env f_csm f_prd cf g_csm g_prd cg ->
      assert (lcsub_at_leaves (lc_sub_push (LCbind env f_csm f_prd cf g_csm g_prd cg)))
          by (norm_lcsbl true;
              split ();
                apply_lemma (``@lc_sub_push_at_leaves);
                let _ = forall_intro () in apply_lemma (``@lc_sub_push_at_leaves))
  | LCsub  env csm prd cf csm' prd' prd_f ->
      lc_sub_push_aux_at_leaves _ cf csm' prd' prd_f

and lc_sub_push_aux_at_leaves
      (env : vprop_list) (#a0 : Type u#a) (#t0 : M.prog_tree a0) (#csm0 : csm_t env) (#prd0 : prd_t a0)
      (ct0 : lin_cond env t0 csm0 prd0)
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
    begin fun (*LCspec*) a sp s sh csm_f -> fun csm' prd' prd_f ->
      assert (goal (LCspec env #a #sp s sh csm_f) csm' prd' prd_f)
          by (norm_lcsbl true; trivial ())
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
                        L.length (filter_mask (mask_not (bind_g_csm' env f_csm (f_prd x) g_csm))
                                              (res_env env f_csm (f_prd x))))
              = filter_bind_g_csm' env f_csm (f_prd x) g_csm in
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
    begin fun (*LCsub*)  a f csm0 prd0 cf csm1 prd1 prd_f1 -> fun csm2 prd2 prd_f2 ->
      assert (goal (LCsub env #a #f csm0 prd0 cf csm1 prd1 prd_f1) csm2 prd2 prd_f2)
          by (norm_lcsbl false;
              apply (`rew_lcsub_at_leaves_csm);
              apply_lemma (`lc_sub_push_aux_at_leaves);
              smt ())
    end csm'0 prd'0 prd_f0
#pop-options
