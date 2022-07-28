module Experiment.Steel.Repr.LV_to_M

module L      = FStar.List.Pure
module Fl     = Learn.FList
module Veq    = Experiment.Steel.VEquiv
module Perm   = Learn.Permutation
module TLogic = Learn.Tactics.Logic

open FStar.Tactics

// FIXME: without `--ide_id_info_off` the interactive mode takes a lot of time
#set-options "--ide_id_info_off"

#push-options "--ifuel 0 --fuel 0"
let extract_eij_framed_equiv
      (env : vprop_list) (pre : M.pre_t) (csm_f : eq_injection_l pre env)
      (sl : sl_f env)
  : Lemma (extract_vars (eij_framed_equiv env pre csm_f) sl
        == append_vars (eij_sl (L.index csm_f) sl) (filter_sl (mask_not (eij_trg_mask csm_f)) sl))
  =
    Ll.pat_append ();
    let m = eij_trg_mask csm_f in
    let flt1 = filter_mask (mask_not m) env in
    let l1 = L.(filter_mask m env @ flt1) in
    let l2 = L.(pre @ flt1) in
    let f0 : vequiv_perm env l1 = mask_pequiv_append m env in
    let f1 : vequiv_perm l1  l2 = Perm.(pequiv_append (eij_equiv csm_f) (pequiv_refl flt1)) in
    calc (==) {
      extract_vars (eij_framed_equiv env pre csm_f) sl <: sl_f l2;
    == { }
      extract_vars Perm.(pequiv_trans f0 f1) sl;
    == { Fl.apply_pequiv_trans (vequiv_perm_sl f0) (vequiv_perm_sl f1) sl }
      extract_vars f1 (extract_vars f0 sl);
    == { filter_mask_fl_perm_append m (vprop_list_sels_t env) sl }
      extract_vars f1 (Fl.append (filter_sl m sl) (filter_sl (mask_not m) sl));
    == { Fl.apply_pequiv_append (vequiv_perm_sl (eij_equiv csm_f)) (vequiv_perm_sl (Perm.pequiv_refl flt1))
                                (filter_sl m sl) (filter_sl (mask_not m) sl) }
      Fl.append (extract_vars (eij_equiv csm_f) (filter_sl m sl))
                (extract_vars (Perm.pequiv_refl flt1) (filter_sl (mask_not m) sl));
    == { }
      Fl.append (extract_vars (eij_equiv csm_f) (filter_sl m sl)) (filter_sl (mask_not m) sl);
    == { extract_eij_equiv csm_f sl }
      Fl.append #(vprop_list_sels_t pre) (eij_sl (L.index csm_f) sl) (filter_sl (mask_not m) sl);
    }

#push-options "--z3rlimit 60"
let eij_split1_equiv (src0 src1 #trg : vprop_list) (eij : eq_injection_l L.(src0 @ src1) trg)
                     (sl : sl_f trg)
  : Lemma (extract_vars (Perm.pequiv_sym (eij_equiv (eij_split1 src0 src1 eij)))
                                (split_vars src0 src1 (eij_sl (L.index eij) sl))._2
        == filter_sl (eij_trg_mask (eij_split1 src0 src1 eij))
             (filter_sl (mask_not (eij_trg_mask (eij_split src0 src1 eij)._1)) sl))
  =
    let n0 = L.length src0 in
    let n1 = L.length src1 in
    let r0, r1 = eij_split src0 src1 eij in
    let r1' = eij_split1 src0 src1 eij in
    let m   = mask_not (eij_trg_mask r0) in
    let eqv = eij_equiv r1' in
    let sl0 = (split_vars src0 src1 (eij_sl (L.index eij) sl))._2 in
    let sl1 = filter_sl (eij_trg_mask r1') (filter_sl m sl) in

    Fl.flist_extensionality sl0 (extract_vars eqv sl1)
       (fun i ->
         assert (i < n1);
         L.lemma_splitAt_reindex_right n0 eij i;

         let j = L.index eij (n0 + i) in
         let v = L.index trg j        in
         let sl_j : v.t  = sl j       in

         assert (L.index src1 i == v);
         let sl0_i : v.t = sl0 i in
         assert (sl0_i == sl_j)
           by (norm [delta_only [`%split_vars; `%eij_sl;
                                 `%Mktuple2?._2; `%Fl.splitAt_ty; `%U.cast; `%Fl.mk_flist;
                                 `%FunctionalExtensionality.on_domain];
                     iota];
               smt ());

         U.assert_by (L.index (eij_trg_mask r1') (L.index r1' i)) (fun () ->
           L.lemma_index_memP r1' i);
         U.assert_by (L.index m (L.index r1 i)) (fun () ->
           Ll.memP_iff (L.index r1 i) r0; Ll.splitAt_index n0 eij);
         calc (==) {
           mask_pull m (mask_pull (eij_trg_mask r1') (eqv i)) <: int;
         == { U.by_refl () }
           mask_pull m (mask_pull (eij_trg_mask r1') (mask_push (eij_trg_mask r1') (L.index r1' i)));
         == { }
           mask_pull m (L.index r1' i);
         == { }
           L.index r1 i;
         == { }
           j;
         }
       );
    extract_vars_sym_l eqv sl1
#pop-options

#push-options "--z3rlimit 20"
let extract_spec_post_equiv
      (env : vprop_list) (pre post ro : vprop_list) (pre_f : eq_injection_l L.(pre @ ro) env)
      (sl0 : sl_f env) (sl_post : sl_f post)
  : Lemma (extract_vars (spec_post_equiv env pre post ro pre_f)
                        (append_vars (append_vars sl_post (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2)
                                     (filter_sl (mask_not (eij_trg_mask pre_f)) sl0))
        == append_vars sl_post (filter_sl (mask_not (eij_trg_mask (eij_split pre ro pre_f)._1)) sl0))
  =
    let m_trg  = eij_trg_mask pre_f                 in
    let csm_f  = (eij_split pre ro pre_f)._1        in
    let m_trg0 = eij_trg_mask csm_f                 in
    let env1   = filter_mask (mask_not m_trg0) env  in
    let ro_f1  : eq_injection_l ro env1
               = eij_split1 pre ro pre_f            in
    let m_trg1 = eij_trg_mask ro_f1                 in
    let flt0   = filter_mask m_trg1 env1            in
    let flt1   = filter_mask (mask_not m_trg1) env1 in

    Ll.pat_append ();
    L.append_assoc post ro (filter_mask (mask_not m_trg) env);
    eij_split1_trg_mask pre ro pre_f;
    mask_not_comp_or m_trg0 m_trg1;
    filter_mask_and (mask_not m_trg0) (mask_not m_trg1) env;

    let f0 : vequiv_perm ro flt0
      = Perm.pequiv_sym (eij_equiv ro_f1)                    in
    let f1 : vequiv_perm L.(flt0 @ flt1) env1
      = mask_pequiv_append' m_trg1 env1                      in
    let f2_0 = Perm.pequiv_append f0 (Perm.pequiv_refl flt1) in
    let f2_1 = Perm.pequiv_trans f2_0 f1                     in
    let f2 : vequiv_perm L.(post @ (ro @ flt1)) L.(post @ env1)
      = Perm.pequiv_append (Perm.pequiv_refl post) f2_1
    in
    let sl_ro   = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2 in
    let sl_rem  = filter_sl (mask_not m_trg ) sl0 in
    let sl_env1 = filter_sl (mask_not m_trg0) sl0
    in
    calc (==) {
      extract_vars (spec_post_equiv env pre post ro pre_f)
                   (append_vars (append_vars sl_post sl_ro) sl_rem);
    == { }
      extract_vars f2 (append_vars (append_vars sl_post sl_ro) sl_rem);
    == { Fl.append_assoc sl_post sl_ro sl_rem;
         Fl.apply_pequiv_append (vequiv_perm_sl (Perm.pequiv_refl post))
                                (vequiv_perm_sl f2_1)
                                sl_post (append_vars sl_ro sl_rem) }
      append_vars sl_post (extract_vars f2_1 (append_vars sl_ro sl_rem));
    == { Fl.apply_pequiv_trans (vequiv_perm_sl f2_0) (vequiv_perm_sl f1) (append_vars sl_ro sl_rem);
         Fl.apply_pequiv_append (vequiv_perm_sl f0)
                                (vequiv_perm_sl (Perm.pequiv_refl flt1))
                                sl_ro sl_rem }
      append_vars sl_post (extract_vars f1 (append_vars (extract_vars f0 sl_ro) sl_rem));
    == { eij_split1_equiv pre ro pre_f sl0;
         filter_mask_fl_and (mask_not m_trg0) (mask_not m_trg1) (vprop_list_sels_t env) sl0 }
      append_vars sl_post (extract_vars f1 (append_vars (filter_sl           m_trg1  sl_env1)
                                                        (filter_sl (mask_not m_trg1) sl_env1)));
    == { filter_mask_fl_perm_append' m_trg1 _ sl_env1 }
      append_vars sl_post sl_env1;
    }
#pop-options

let extract_sub_prd_framed_equiv
      (env : vprop_list) 
      (csm0 : csm_t env) (prd0 : vprop_list)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : vprop_list)
      (veq  : vequiv_perm (sub_prd env csm0 prd0 csm1) prd1)
      (sl0 : sl_f prd0) (sl1 : sl_f (filter_mask (mask_not csm0) env))
  : Lemma (filter_bind_csm env csm0 csm1;
       extract_vars (sub_prd_framed_equiv env csm0 prd0 csm1 prd1 veq) (append_vars sl0 sl1)
    == append_vars (extract_vars veq (append_vars sl0 (filter_sl csm1 sl1)))
                   (filter_sl (mask_not csm1) sl1))
  =
    Ll.pat_append ();
    filter_bind_csm env csm0 csm1;
    let env1 = filter_mask (mask_not csm0) env  in
    let flt1 = filter_mask csm1 env1            in
    let flt2 = filter_mask (mask_not csm1) env1 in
    L.append_assoc prd0 flt1 flt2;

    let f0  : vequiv_perm L.(prd0 @ flt1) prd1 = U.cast _ veq    in
    let f0' : vequiv_perm L.(prd0 @ flt1 @ flt2) L.(prd1 @ flt2)
      = U.cast _ (Perm.pequiv_append f0 (Perm.pequiv_refl flt2)) in
    let f1  : vequiv_perm env1 L.(flt1 @ flt2)
       = mask_pequiv_append csm1 env1                            in
    let f1' : vequiv_perm L.(prd0 @ env1) L.(prd0 @ flt1 @ flt2)
      = Perm.pequiv_append (Perm.pequiv_refl prd0) f1            in
    let sls0 : sl_f L.(prd0 @ env1) = Fl.append sl0 sl1          in
    let sl_flt1 : sl_f flt1 = filter_sl csm1 sl1                 in
    let sl_flt2 : sl_f flt2 = filter_sl (mask_not csm1) sl1      in

    calc (==) {
      extract_vars (sub_prd_framed_equiv env csm0 prd0 csm1 prd1 veq) (append_vars sl0 sl1)
        <: sl_f L.(prd1 @ flt2);
    == { }
      extract_vars (Perm.pequiv_trans f1' f0') sls0;
    == { Fl.apply_pequiv_trans (vequiv_perm_sl f1') (vequiv_perm_sl f0') sls0 }
      extract_vars f0' (extract_vars f1' sls0);
    == { Fl.apply_pequiv_append (vequiv_perm_sl (Perm.pequiv_refl prd0))
                                (vequiv_perm_sl f1)
                                sl0 sl1 }
      extract_vars f0' (append_vars sl0 (extract_vars f1 sl1));
    == { filter_mask_fl_perm_append csm1 (vprop_list_sels_t env1) sl1 }
      extract_vars f0' (append_vars sl0 (append_vars sl_flt1 sl_flt2));
    == { Fl.append_assoc sl0 sl_flt1 sl_flt2 }
      extract_vars f0' (append_vars (append_vars sl0 sl_flt1) sl_flt2);
    == { Fl.apply_pequiv_append (vequiv_perm_sl f0)
                                (vequiv_perm_sl (Perm.pequiv_refl flt2))
                                (append_vars sl0 sl_flt1) sl_flt2 }
      append_vars (extract_vars veq (append_vars sl0 sl_flt1)) sl_flt2;
    }

#pop-options


let bind_g_csm'1_res_env_f
      (env : vprop_list) (b : Type)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
  : Lemma (res_env_f (res_env env f_csm f_prd) (bind_g_csm'1 env f_csm f_prd g_csm) g_prd
        == res_env_f env (bind_csm env f_csm g_csm) g_prd)
  =
    U.funext_eta
        (res_env_f (res_env env f_csm f_prd) (bind_g_csm'1 env f_csm f_prd g_csm) g_prd)
        (res_env_f env (bind_csm env f_csm g_csm) g_prd)
        (_ by (trefl ())) (_ by (trefl ()))
        (fun (x : b) -> filter_bind_g_csm'1 env f_csm f_prd g_csm)

(**) #push-options "--ifuel 0 --fuel 0 --z3rlimit 20"
(**) private let __begin_opt_0 = ()
(**) #pop-options
(**) private let __end_opt_0 = ()

#push-options "--ifuel 0 --fuel 0 --z3rlimit 20"
let extract_gen_post_equiv
      (env : vprop_list) (pre post ro : vprop_list) (pre_f : Perm.pequiv_list env L.(pre @ ro))
      (sl0 : sl_f env) (sl_post : sl_f post)
  : Lemma (extract_vars (gen_post_equiv env pre post ro pre_f)
                        (append_vars sl_post (split_vars pre ro (extract_vars (Perm.perm_f_of_list pre_f) sl0))._2)
        == append_vars sl_post
                (filter_sl (mask_not (eij_trg_mask (eij_split pre ro (eij_of_perm_l pre_f))._1)) sl0))
  =
    
    let pre_f' = eij_of_perm_l pre_f               in
    let m   = mask_not (eij_trg_mask pre_f')       in
    let flt = filter_mask m env                    in
    let f : vequiv_perm L.((post @ ro) @ flt)
                          (res_env env (eij_trg_mask (eij_split pre ro pre_f')._1) post)
          = spec_post_equiv env pre post ro pre_f' in
    U.assert_by (flt == []) (fun () ->
      filter_mask_false m env (fun i -> eij_of_perm_l_trg pre_f i));
    let sl0' = append_vars sl_post (split_vars pre ro (extract_vars (Perm.perm_f_of_list pre_f) sl0))._2 in
    calc (==) {
      extract_vars (gen_post_equiv env pre post ro pre_f) sl0';
    == { }
      extract_vars f sl0';
    == { 
         calc (==) {
           vprop_list_sels_t flt;
         == { }
           vprop_list_sels_t [];
         == { U.by_refl () }
           [];
         };
         Fl.nil_uniq (filter_sl m sl0 <: sl_f flt);
         Fl.flist_extensionality
           (extract_vars (Perm.perm_f_of_list pre_f) sl0)
           (eij_sl #L.(pre@ro) (L.index pre_f') sl0)
           (fun i -> ())
       }
      extract_vars f (append_vars (append_vars sl_post (split_vars pre ro (eij_sl (L.index pre_f') sl0))._2)
                                  (filter_sl m sl0));
    == { extract_spec_post_equiv env pre post ro pre_f' sl0 sl_post }
      append_vars sl_post (filter_sl (mask_not (eij_trg_mask (eij_split pre ro pre_f')._1)) sl0);
    }
#pop-options


#push-options "--ifuel 0 --fuel 1"
let inv_lcsub_at_leaves__LCsub
      (#env : vprop_list) (#a : Type) (#f : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (cf : lin_cond env f csm prd)
      (csm' : csm_t (filter_mask (mask_not csm) env)) (prd' : prd_t a)
      (prd_f : ((x : a) -> Perm.pequiv_list (sub_prd env csm (prd x) csm') (prd' x)))
  : Lemma (requires lcsub_at_leaves (LCsub env csm prd cf csm' prd' prd_f))
          (ensures  LCspec? cf \/ LCgen? cf)
  =
    match_lin_cond cf
      (fun a f csm prd cf -> (csm' : _) -> (prd' : _) -> (prd_f : _) ->
        squash (Pervasives.norm [delta_only [`%lcsub_at_leaves]; iota; zeta]
                 (lcsub_at_leaves (LCsub env csm prd cf csm' prd' prd_f)) ==>
                LCspec? cf \/ LCgen? cf))
      (fun (*LCspec*)  a sp s sh pre_f -> fun csm' prd' prd_f -> ())
      (fun (*LCret*)   a x sl_hint prd csm_f -> fun csm' prd' prd_f -> ())
      (fun (*LCbind*)  a b f g f_csm f_prd cf g_csm g_prd cg -> fun csm' prd' prd_f -> ())
      (fun (*LCbindP*) a b wp g csm0 prd0 cg -> fun csm1 prd1 prd_f -> ())
      (fun (*LCif*)    a guard thn els csm0 prd0 cthn cels -> fun csm1 prd1 prd_f -> ())
      (fun (*LCgen*)   a gen_tac gen_c c pre_f -> fun csm2 prd2 prd_f2 -> ())
      (fun (*LCsub*)   a f csm0 prd0 cf csm1 prd1 prd_f1 -> fun csm2 prd2 prd_f2 -> ())
      csm' prd' prd_f
#pop-options

(**) #push-options "--ifuel 1 --fuel 1 --z3rlimit 30"
(**) private let __begin_opt_1 = ()
(**) #pop-options
(**) private let __end_opt_1 = ()

(*** Soundness *)

#push-options "--ifuel 0 --fuel 0"

let sound_repr_M_of_LV
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd {lcsub_at_leaves lc})
  : prop
  = sound_M_of_LV lc (repr_M_of_LV lc)

let intro_sound_M_of_LV
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd) (mc : lc_to_M lc)
      (pf_req : (sl0 : sl_f env) ->
                squash (M.tree_req t mc sl0 <==> tree_req lc sl0))
      (pf_ens : (sl0 : sl_f env) -> (res : a) -> (sl1 : sl_f (prd res)) ->
                (sl_rem : sl_f (filter_mask (mask_not csm) env)) ->
                squash (M.tree_ens t mc sl0 res (res_env_app sl1 sl_rem) <==>
                        (tree_ens lc sl0 res sl1 /\ sl_rem == filter_sl (mask_not csm) sl0)))
  : squash (sound_M_of_LV lc mc)
  =
    introduce forall (sl0 : sl_f env) . M.tree_req t mc sl0 <==> tree_req lc sl0
      with pf_req sl0;
    introduce forall (sl0 : sl_f env) (res : a) (sl1 : sl_f (prd res))
                (sl_rem : sl_f (filter_mask (mask_not csm) env)) .
                M.tree_ens t mc sl0 res (res_env_app sl1 sl_rem) <==>
                (tree_ens lc sl0 res sl1 /\ sl_rem == filter_sl (mask_not csm) sl0)
      with pf_ens sl0 res sl1 sl_rem

let sound_M_of_LV_req
      #env #a #t #csm #prd
      (#lc : lin_cond env #a t csm prd) (#mc : lc_to_M lc)
      (pf : squash (sound_M_of_LV lc mc))
      (sl0 : sl_f env) 
  : squash (M.tree_req t mc sl0 <==> tree_req lc sl0)
  = ()

let sound_M_of_LV_ens
      #env #a #t #csm #prd
      (#lc : lin_cond env #a t csm prd) (#mc : lc_to_M lc)
      (pf : squash (sound_M_of_LV lc mc))
      (sl0 : sl_f env) (res : a) (sl1 : sl_f (prd res)) (sl_rem : sl_f (filter_mask (mask_not csm) env))
  : squash (M.tree_ens t mc sl0 res (res_env_app sl1 sl_rem) <==>
             (tree_ens lc sl0 res sl1 /\ sl_rem == filter_sl (mask_not csm) sl0))
  = ()


let vequiv_of_perm_sel_eq_list
      (#pre #post : vprop_list) (f : vequiv_perm pre post)
      (sl0 : sl_f pre) (sl1 : sl_f post)
  : squash Veq.(veq_sel_eq (veq_eq_sl (veq_of_list (veq_to_list (vequiv_of_perm_eq f)))) sl0 sl1
                <==> sl1 == extract_vars f sl0)
  = Veq.vequiv_of_perm_sel_eq f sl0 sl1

#pop-options

let vequiv_refl_sel_eq
      (#v: vprop_list) (sl0 : sl_f v) (sl1 : sl_f v)
  : squash Veq.(veq_sel_eq (veq_eq_sl (veq_of_list (vequiv_refl_eq v))) sl0 sl1 <==> sl1 == sl0)
  = introduce _ /\  _
       with introduce _ ==> _ with _ .
            Fl.flist_extensionality sl1 sl0 (fun i -> ())
        and ()


let rew_iff_LV2M () : Tac unit =
  TLogic.rew_iff (fun r -> first [
    (fun () -> apply (`vequiv_refl_sel_eq));
    (fun () -> apply (`vequiv_of_perm_sel_eq_list));
    (fun () -> apply (`rew_append_var_inj));
    (fun () -> apply (`rew_append_var_inj'); later ());
    (fun () -> apply (`rew_forall_sl_f_app); r ());
    (fun () -> apply (`rew_exists_sl_f_app); r ())
  ])

let rew_iff_l_LV2M (smp : bool) : Tac unit =
  apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm (if smp then [simplify] else [])


let norm_sound_LV2M () : Tac unit =
  norm [delta_only [`%repr_M_of_LV; `%repr_M_of_LV__tcs; `%repr_M_of_LV__tcs_sub;
                    `%M.tree_req; `%M.spec_req; `%M.return_req; `%M.bind_req; `%M.gen_req;
                    `%M.tree_ens; `%M.spec_ens; `%M.return_ens; `%M.bind_ens; `%M.gen_ens;
                    `%Veq.vequiv_of_perm; `%Veq.vequiv_refl;
                    `%Veq.Mkvequiv?.veq_req; `%Veq.Mkvequiv?.veq_ens; `%Veq.Mkvequiv?.veq_eq; `%Veq.veq_ens1;
                    `%tree_req; `%tree_ens; `%Mklc_gen_cond?.lcg_s;
                    `%res_env_app; `%res_env_f; `%res_env; `%sub_prd_sl];
        delta_attr [`%Learn.Tactics.Util.__tac_helper__];
        iota; zeta]

let tac_sound_LV2M () : Tac unit =
  norm_sound_LV2M ();
  rew_iff_l_LV2M true;
  l_to_r [`extract_eij_framed_equiv];
  rew_iff_l_LV2M false


#push-options "--ifuel 0 --fuel 1"

let sound_repr_M_of_LV__LCspec
      (env : vprop_list)
      (a : Type) (sp : M.spec_r a -> Type)
      (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (sh : sp (M.Mkspec_r pre post ro req ens))
      (pre_f : eq_injection_l L.(pre @ ro) env)
  : squash (sound_repr_M_of_LV (LCspec env #a #sp (M.Mkspec_r pre post ro req ens) sh pre_f))
  =
    intro_sound_M_of_LV _ _
      (fun sl0 ->
        let split_sl0_lem = split_vars_append pre ro (eij_sl (L.index pre_f) sl0) in
        let sl0_pre = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._1         in
        let sl0_ro  = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2         in
        let sl0_rem = filter_sl (mask_not (eij_trg_mask pre_f)) sl0               in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
          l_to_r [`extract_eij_framed_equiv];
          apply (`TLogic.rew_iff_left);
              l_to_r [``@split_sl0_lem];
              rew_iff_LV2M ();
              norm [];
          // re-running rew_iff_LV2M since there is a nested append
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [];
          // We rewrite [forall sl' . sl' = sl0_* ==> p sl'] into [p sl0_*]
          TLogic.(
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_pre)); smt (); norm [simplify];
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_ro )); smt (); norm [simplify];
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_rem)); smt ();
              norm_sound_LV2M (); norm [delta_only [`%split_vars]; simplify]
          );
          smt ()))
      (fun sl0 x sl1 sl_rem ->
        let split_sl0_lem = split_vars_append pre ro (eij_sl (L.index pre_f) sl0) in
        let sl0_pre = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._1         in
        let sl0_ro  = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2         in
        let sl0_rem = filter_sl (mask_not (eij_trg_mask pre_f)) sl0               in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          rew_iff_l_LV2M true;
          l_to_r [`extract_eij_framed_equiv];
          apply (`TLogic.rew_iff_left);
              l_to_r [``@split_sl0_lem];
              rew_iff_LV2M ();
              norm [];
          rew_iff_l_LV2M false;
          TLogic.(
            apply (`rew_iff_left); apply_raw (`rew_exists_eq (`@sl0_pre));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply (`rew_exists_eq (`@sl0_ro ));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply_raw (`rew_exists_eq (`@sl0_rem));
              smt (); norm_sound_LV2M (); norm [simplify]
          );
          l_to_r [`extract_spec_post_equiv];
          rew_iff_l_LV2M false;
          smt ()))

let sound_repr_M_of_LV__LCret
      (env : vprop_list)
      (a : Type) (x : a) (sl_hint : option (M.post_t a))
      (prd : prd_t a) (csm_f : eq_injection_l (prd x) env)
  : squash (sound_repr_M_of_LV (LCret env #a #x #sl_hint prd csm_f))
  =
    intro_sound_M_of_LV _ _
      (fun sl0 -> ())
      (fun sl0 x' sl1 sl_rem ->
        _ by (tac_sound_LV2M ();
                // [rew_append_var_inj'] generates an additional goal because the typing relies on [x' == x]
                smt ();
              smt ()))

let sound_repr_M_of_LV__LCbind
      (env : vprop_list)
      (a : Type) (b : Type) (f : M.prog_tree a) (g : (a -> M.prog_tree b))
      (f_csm : csm_t env) (f_prd : prd_t a)
      (cf : lin_cond env f f_csm f_prd)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (cg : ((x : a) ->
        lin_cond (res_env env f_csm (f_prd x)) (g x) (bind_g_csm'1 env f_csm (f_prd x) g_csm) g_prd))

      (_ : squash (lcsub_at_leaves (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg)))
      (h_f : squash (sound_repr_M_of_LV cf))
      (h_g : (x : a) -> squash (sound_repr_M_of_LV (cg x)))
  : squash (sound_repr_M_of_LV (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg))
  =
    introduce forall (x : a) .
            res_env_f env (bind_csm env f_csm g_csm) g_prd
         == res_env_f (res_env env f_csm (f_prd x)) (bind_g_csm'1 env f_csm (f_prd x) g_csm) g_prd
      with bind_g_csm'1_res_env_f env b f_csm (f_prd x) g_csm g_prd;
    introduce forall (x : a) .
            filter_mask (mask_not (bind_g_csm'1 env f_csm (f_prd x) g_csm)) (res_env env f_csm (f_prd x))
         == filter_mask (mask_not (bind_csm env f_csm g_csm)) env
      with filter_bind_g_csm'1 env f_csm (f_prd x) g_csm;
    let h_g_req x sl0
      : squash (M.tree_req (g x) #_ #(res_env_f env (bind_csm env f_csm g_csm) g_prd) (repr_M_of_LV (cg x)) sl0
             <==> tree_req (cg x) sl0)
      = sound_M_of_LV_req (h_g x) sl0
    in let h_g_ens x (sl0 : sl_f (res_env env f_csm (f_prd x))) y sl1 sl_rem
      : squash (M.tree_ens (g x)
                  #_ #(res_env_f env (bind_csm env f_csm g_csm) g_prd) (repr_M_of_LV (cg x))
                  sl0 y (res_env_app sl1 sl_rem)
            <==> (tree_ens (cg x) sl0 y sl1 /\
                sl_rem == filter_sl (mask_not (bind_g_csm'1 env f_csm (f_prd x) g_csm)) sl0))
      = sound_M_of_LV_ens (h_g x) sl0 y sl1 sl_rem
    in
    intro_sound_M_of_LV _ _
      (fun sl0 ->
        _ by (norm_sound_LV2M ();
              apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [];
              apply (`TLogic.rew_iff_left); TLogic.rew_iff (fun r -> first [
                  (fun () -> apply (`sound_M_of_LV_req (`@h_f)));
                  (fun () -> apply (`sound_M_of_LV_ens (`@h_f)));
                  (fun () -> apply (``@h_g_req))
                ]); norm [];
              smt ()))
      (fun sl0 y sl2 sl_rem ->
        _ by (norm_sound_LV2M ();
              apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [];
              apply (`TLogic.rew_iff_left); TLogic.rew_iff (fun r -> first [
                  (fun () -> apply (`sound_M_of_LV_ens (`@h_f)));
                  (fun () -> apply (``@h_g_ens))
                ]); norm [];
              l_to_r [`filter_sl_bind_g_csm'; `filter_sl_bind_csm];
              smt ()
              ))

let sound_repr_M_of_LV__LCbindP
      (env : vprop_list)
      (a : Type) (b : Type) (wp : pure_wp a) (g : a -> M.prog_tree b)
      (csm : csm_t env) (prd : prd_t b)
      (cg : (x : a) -> lin_cond env (g x) csm prd)

      (_ : squash (lcsub_at_leaves (LCbindP env #a #b #wp #g csm prd cg)))
      (h_g : (x : a) -> squash (sound_repr_M_of_LV (cg x)))
  : squash (sound_repr_M_of_LV (LCbindP env #a #b #wp #g csm prd cg))
  =
    FStar.Classical.forall_intro_squash_gtot h_g;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    intro_sound_M_of_LV _ _ (fun sl0 -> ()) (fun sl0 y sl2 sl_rem -> ())


let sound_repr_M_of_LV__LCif
      (env : vprop_list)
      (a : Type) (guard : bool) (thn els : M.prog_tree a)
      (csm : csm_t env) (prd : prd_t a)
      (cthn : lin_cond env thn csm prd)
      (cels : lin_cond env els csm prd)

      (_ : squash (lcsub_at_leaves (LCif env #a #guard #thn #els csm prd cthn cels)))
      (h_thn : squash (sound_repr_M_of_LV cthn))
      (h_els : squash (sound_repr_M_of_LV cels))
  : squash (sound_repr_M_of_LV (LCif env #a #guard #thn #els csm prd cthn cels))
  =
    intro_sound_M_of_LV _ _ (fun sl0 -> ()) (fun sl0 y sl2 sl_rem -> ())


let sound_repr_M_of_LV__LCgen
      (env : vprop_list)
      (a : Type) (gen_tac : M.gen_tac_t)
      (gen_c : M.spec_r a -> Type)
      (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (sh : gen_c (M.Mkspec_r pre post ro req ens))
      (pre_f : Perm.pequiv_list env L.(pre @ ro))
      (sf : gen_sf (M.Mkspec_r pre post ro req ens))
  : squash (sound_repr_M_of_LV (LCgen env #a #gen_tac #gen_c (Mklc_gen_cond (M.Mkspec_r pre post ro req ens) sh sf) pre_f))
  =
    intro_sound_M_of_LV _ _
      (fun sl0 ->
        let split_sl0_lem = split_vars_append pre ro (extract_vars (Perm.perm_f_of_list pre_f) sl0) in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          rew_iff_l_LV2M true;
          norm_sound_LV2M (); norm [simplify];
          apply (`TLogic.rew_iff_left);
            l_to_r [``@split_sl0_lem];
            rew_iff_LV2M ();
            norm [];
          smt ()))
      (fun sl0 x sl1 sl_rem ->
        let extr_sl0      = extract_vars (Perm.perm_f_of_list pre_f) sl0 in
        let split_sl0_lem = split_vars_append pre ro extr_sl0            in
        let sl0_pre       = (split_vars pre ro extr_sl0)._1              in
        let sl0_ro        = (split_vars pre ro extr_sl0)._2              in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          rew_iff_l_LV2M true;
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left);
            l_to_r [``@split_sl0_lem];
            rew_iff_LV2M ();
            norm [];
          TLogic.(
            apply (`rew_iff_left); apply_raw (`rew_exists_eq (`@sl0_pre));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply (`rew_exists_eq (`@sl0_ro ));
              smt (); norm [simplify]
          );
          l_to_r [`extract_gen_post_equiv];
          rew_iff_l_LV2M false;
          smt ()))

#pop-options

#push-options "--fuel 0 --ifuel 0"

let extract_pequiv_trans #v0 #v1 #v2 (f : vequiv_perm v0 v1) (g : vequiv_perm v1 v2) (sl : sl_f v0)
  : Lemma (extract_vars (Perm.pequiv_trans f g) sl == extract_vars g (extract_vars f sl))
  =
    Fl.apply_pequiv_trans (vequiv_perm_sl f) (vequiv_perm_sl g) sl


let force_M_tree_req #a #t #pre #post (c : M.tree_cond #a t pre post) sl0
  : squash (M.tree_req t c sl0 <==> M.tree_req t c sl0)
  = ()

let force_M_tree_ens #a #t #pre #post (c : M.tree_cond #a t pre post) sl0 x sl1
  : squash (M.tree_ens t c sl0 x sl1 <==> M.tree_ens t c sl0 x sl1)
  = ()

// TODO?: factorize with LCspec
let sound_repr_M_of_LV__LCsub_LCspec
      (env : vprop_list)
      (a : Type) (sp : M.spec_r a -> Type)
      (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (sh : sp (M.Mkspec_r pre post ro req ens))
      (pre_f : eq_injection_l L.(pre @ ro) env)
      (csm1 : csm_t (filter_mask (mask_not (eij_trg_mask (eij_split pre ro pre_f)._1)) env))
      (prd1 : prd_t a)
      (prd_f1 : (x : a) ->
              Perm.pequiv_list (sub_prd env (eij_trg_mask (eij_split pre ro pre_f)._1) (post x) csm1) (prd1 x))
  : (let lc = LCsub env ((eij_trg_mask (eij_split pre ro pre_f)._1)) post
                    (LCspec env #a #sp (M.Mkspec_r pre post ro req ens) sh pre_f)
                    csm1 prd1 prd_f1
     in squash (lcsub_at_leaves lc /\ sound_repr_M_of_LV lc))
  = introduce _ /\ _
    with _ by (norm [delta_only [`%lcsub_at_leaves]; iota; zeta]; trivial ())
    and intro_sound_M_of_LV _ _
      (fun sl0 ->
        let split_sl0_lem = split_vars_append pre ro (eij_sl (L.index pre_f) sl0) in
        let sl0_pre = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._1         in
        let sl0_ro  = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2         in
        let sl0_rem = filter_sl (mask_not (eij_trg_mask pre_f)) sl0               in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          // For some reason (maybe the strict_on_arguments + type ascription ?) the reduction of
          // M.tree_req is blocked. The following line somehow enable the reduction.
          apply (`TLogic.rew_iff_left); apply (`force_M_tree_req);
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
          l_to_r [`extract_eij_framed_equiv];
          apply (`TLogic.rew_iff_left);
              l_to_r [``@split_sl0_lem];
              rew_iff_LV2M ();
              norm [];
          // re-running rew_iff_LV2M since there is a nested append
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [];
          // We rewrite [forall sl' . sl' = sl0_* ==> p sl'] into [p sl0_*]
          TLogic.(
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_pre)); smt (); norm [simplify];
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_ro )); smt (); norm [simplify];
            apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_rem)); smt ();
              norm_sound_LV2M (); norm [delta_only [`%split_vars]; simplify]
          );
          smt ()))
      (fun sl0 x sl1 sl_rem ->
        let split_sl0_lem = split_vars_append pre ro (eij_sl (L.index pre_f) sl0) in
        let sl0_pre = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._1         in
        let sl0_ro  = (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2         in
        let sl0_rem = filter_sl (mask_not (eij_trg_mask pre_f)) sl0               in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); apply (`force_M_tree_ens);
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
          l_to_r [`extract_eij_framed_equiv];
          apply (`TLogic.rew_iff_left);
            l_to_r [``@split_sl0_lem];
            rew_iff_LV2M ();
            norm [];
          rew_iff_l_LV2M false;
          with_policy SMT TLogic.(fun () ->
            apply (`rew_iff_left); apply_raw (`rew_exists_eq (`@sl0_pre));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply (`rew_exists_eq (`@sl0_ro ));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply_raw (`rew_exists_eq (`@sl0_rem));
              smt (); norm_sound_LV2M (); norm [simplify]
          );
          norm [delta_only [`%spec_sub_post_equiv]];
          norm_sound_LV2M ();
          l_to_r [`extract_pequiv_trans];
          l_to_r [`extract_spec_post_equiv];
          with_policy Goal (fun () ->
          l_to_r [`extract_sub_prd_framed_equiv]); later ();
            // guard
            norm_sound_LV2M (); norm [simplify]; smt ();
          rew_iff_l_LV2M false;
            // additional goal generated by [rew_append_var_inj']
            seq explode (fun () -> try trefl () with | _ -> ());
            apply_lemma (`filter_bind_csm);
          norm [delta_only [`%U.cast]; iota];
          l_to_r [`filter_sl_bind_csm];
          smt ()
          ))

let sound_repr_M_of_LV__LCsub_LCgen
      (env : vprop_list)
      (a : Type) (gen_tac : M.gen_tac_t)
      (gen_c : M.spec_r a -> Type)
      (pre : M.pre_t) (post : M.post_t a) (ro : vprop_list)
      (req : sl_f pre -> sl_f ro -> Type0) (ens : sl_f pre -> (x : a) -> sl_f (post x) -> sl_f ro -> Type0)
      (sh : gen_c (M.Mkspec_r pre post ro req ens))
      (pre_f : Perm.pequiv_list env L.(pre @ ro))
      (sf : gen_sf (M.Mkspec_r pre post ro req ens))
      (csm1 : csm_t (filter_mask (mask_not (eij_trg_mask (eij_split pre ro (eij_of_perm_l pre_f))._1)) env))
      (prd1 : prd_t a)
      (prd_f1 : (x : a) ->
              Perm.pequiv_list
                (sub_prd env (eij_trg_mask (eij_split pre ro (eij_of_perm_l pre_f))._1) (post x) csm1)
                (prd1 x))
  : (let lc = LCsub env ((eij_trg_mask (eij_split pre ro (eij_of_perm_l pre_f))._1)) post
                    (LCgen env #a #gen_tac #gen_c (Mklc_gen_cond (M.Mkspec_r pre post ro req ens) sh sf) pre_f)
                    csm1 prd1 prd_f1
     in squash (lcsub_at_leaves lc /\ sound_repr_M_of_LV lc))
  = introduce _ /\ _
    with _ by (norm [delta_only [`%lcsub_at_leaves]; iota; zeta]; trivial ())
    and intro_sound_M_of_LV _ _
      (fun sl0 ->
        let split_sl0_lem = split_vars_append pre ro (extract_vars (Perm.perm_f_of_list pre_f) sl0) in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); apply (`force_M_tree_req);
          norm_sound_LV2M ();
          rew_iff_l_LV2M true;
          apply (`TLogic.rew_iff_left);
            l_to_r [``@split_sl0_lem];
            rew_iff_LV2M ();
            norm [];
          smt ()))
      (fun sl0 x sl1 sl_rem ->
        let extr_sl0      = extract_vars (Perm.perm_f_of_list pre_f) sl0 in
        let split_sl0_lem = split_vars_append pre ro extr_sl0            in
        let sl0_pre       = (split_vars pre ro extr_sl0)._1              in
        let sl0_ro        = (split_vars pre ro extr_sl0)._2              in
        U.assert_by_tac (fun () ->
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); apply (`force_M_tree_ens);
          norm_sound_LV2M ();
          apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
          apply (`TLogic.rew_iff_left);
            l_to_r [``@split_sl0_lem];
            rew_iff_LV2M ();
            norm [];
          TLogic.(
            apply (`rew_iff_left); apply_raw (`rew_exists_eq (`@sl0_pre));
              smt (); norm [simplify];
            apply (`rew_iff_left); apply (`exists_morph_iff); let _ = intro () in
              apply (`rew_exists_eq (`@sl0_ro ));
              smt (); norm [simplify]
          );
          norm [delta_only [`%gen_sub_post_equiv]];
          norm_sound_LV2M ();
          l_to_r [`extract_pequiv_trans];
          l_to_r [`extract_gen_post_equiv];
          with_policy Goal (fun () ->
            l_to_r [`extract_sub_prd_framed_equiv]); later ();
            // guard
            norm_sound_LV2M (); norm [simplify]; smt ();
          rew_iff_l_LV2M false;
            // additional goal generated by [rew_append_var_inj']
            seq explode (fun () -> try trefl () with | _ -> ());
            apply_lemma (`filter_bind_csm);
          norm [delta_only [`%U.cast]; iota];
          l_to_r [`filter_sl_bind_csm];
          smt ()))

#pop-options


#push-options "--ifuel 0 --fuel 1"
let rec repr_M_of_LV_sound
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd {lcsub_at_leaves lc})
  : Lemma (ensures sound_M_of_LV lc (repr_M_of_LV lc)) (decreases lc)
  = match_lin_cond lc
      (fun a t csm prd lc -> squash (lcsub_at_leaves lc) ->
         squash (sound_M_of_LV lc (repr_M_of_LV lc)))
    begin fun (*LCspec*) a sp s sh csm_f -> fun _ ->
      let M.Mkspec_r pre post ro req ens = s in
      sound_repr_M_of_LV__LCspec env a sp pre post ro req ens sh csm_f
    end
    begin fun (*LCret*)  a x sl_hint prd csm_f -> fun _ ->
      sound_repr_M_of_LV__LCret env a x sl_hint prd csm_f
    end
    begin fun (*LCbind*) a b f g f_csm f_prd cf g_csm g_prd cg -> fun _ ->
      sound_repr_M_of_LV__LCbind env a b f g f_csm f_prd cf g_csm g_prd cg ()
        (repr_M_of_LV_sound cf)
        (fun (x : a) -> repr_M_of_LV_sound (cg x))
    end
    begin fun (*LCbindP*) a b wp g csm prd cg -> fun _ ->
      sound_repr_M_of_LV__LCbindP env a b wp g csm prd cg ()
        (fun (x : a) -> repr_M_of_LV_sound (cg x))
    end
    begin fun (*LCif*)   a guard thn els csm prd cthn cels -> fun _ ->
      sound_repr_M_of_LV__LCif env a guard thn els csm prd cthn cels ()
        (repr_M_of_LV_sound cthn)
        (repr_M_of_LV_sound cels)
    end
    begin fun (*LCgen*)   a gen_tac gen_c (Mklc_gen_cond (M.Mkspec_r pre post ro req ens) sh sf) pre_f -> fun _ ->
      sound_repr_M_of_LV__LCgen env a gen_tac gen_c pre post ro req ens sh pre_f sf
    end
    begin fun (*LCsub*)  a0 f0 csm0 prd0 cf csm1 prd1 prd_f1 -> fun _ ->
      inv_lcsub_at_leaves__LCsub cf csm1 prd1 prd_f1;
      match_lin_cond cf
        (fun a f csm0 prd0 cf ->
           (csm1   : csm_t (filter_mask (mask_not csm0) env)) -> (prd1 : prd_t a) ->
           (prd_f1 : ((x : a) -> Perm.pequiv_list (sub_prd env csm0 (prd0 x) csm1) (prd1 x))) ->
           (let lc = LCsub env #a #f csm0 prd0 cf csm1 prd1 prd_f1 in
            squash (lcsub_at_leaves lc) ->
            squash (sound_M_of_LV lc (repr_M_of_LV lc))))
      begin fun (*LCspec*) a sp s sh csm_f -> fun csm1 prd1 prd_f1 _ ->
        let M.Mkspec_r pre post ro req ens = s in
        sound_repr_M_of_LV__LCsub_LCspec env a sp pre post ro req ens sh csm_f csm1 prd1 prd_f1
      end
      (fun (*LCret*)   a x sl_hint prd csm_f -> fun _ _ _ _ -> false_elim ())
      (fun (*LCbind*)  a b f g f_csm f_prd cf g_csm g_prd cg -> fun _ _ _ _ -> false_elim ())
      (fun (*LCbindP*) a b wp g csm prd cg -> fun _ _ _ _ -> false_elim ())
      (fun (*LCif*)    a guard thn els csm prd cthn cels -> fun _ _ _ _ -> false_elim ())
      begin fun (*LCgen*) a gen_tac gen_c (Mklc_gen_cond (M.Mkspec_r pre post ro req ens) sh sf) pre_f ->
            fun csm1 prd1 prd_f1 _ ->
        sound_repr_M_of_LV__LCsub_LCgen env a gen_tac gen_c pre post ro req ens sh pre_f sf csm1 prd1 prd_f1
      end
      (fun (*LCsub*)   a0 f0 csm0 prd0 cf csm1 prd1 prd_f1 -> fun _ _ _ _ -> false_elim ())
      csm1 prd1 prd_f1 ()
    end ()
#pop-options

#push-options "--ifuel 0 --fuel 1"
let repr_M_of_LV_top_sound
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
      (lc : top_lin_cond t pre post {lcsub_at_leaves lc})
  =
    let mc  = repr_M_of_LV_top lc in
    let rem = filter_mask (mask_not (csm_all pre)) pre in
    filter_mask_false (mask_not (csm_all pre)) pre (fun i -> ());
    assert (sl_f rem == Fl.flist []);
    repr_M_of_LV_sound lc;
    introduce forall (sl0 : sl_f pre) (x : a) (sl1 : sl_f (post x)) .
        M.tree_ens t mc sl0 x sl1 <==> tree_ens lc sl0 x sl1
      with
        let sl_rem = filter_sl (mask_not (csm_all pre)) sl0 in
        calc (<==>) {
          M.tree_ens t mc sl0 x sl1;
        <==> { }
          M.tree_ens t mc sl0 x (res_env_app #pre #(csm_all pre) sl1 Fl.nil);
        <==> { }
          tree_ens lc sl0 x sl1 /\ Fl.nil == sl_rem;
        <==> { Fl.nil_uniq sl_rem }
          tree_ens lc sl0 x sl1;
        }
#pop-options
