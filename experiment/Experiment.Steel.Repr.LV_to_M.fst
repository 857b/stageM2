module Experiment.Steel.Repr.LV_to_M

module L      = FStar.List.Pure
module Fl     = Learn.FList
module Veq    = Experiment.Steel.VEquiv
module Perm   = Learn.Permutation
module TLogic = Learn.Tactics.Logic

open FStar.Tactics

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


let bind_g_csm'_res_env_f
      (env : vprop_list) (b : Type)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
  : Lemma (res_env_f (res_env env f_csm f_prd) (bind_g_csm' env f_csm f_prd g_csm) g_prd
        == res_env_f env (bind_csm env f_csm g_csm) g_prd)
  =
    U.funext_eta
        (res_env_f (res_env env f_csm f_prd) (bind_g_csm' env f_csm f_prd g_csm) g_prd)
        (res_env_f env (bind_csm env f_csm g_csm) g_prd)
        (_ by (trefl ())) (_ by (trefl ()))
        (fun (x : b) -> filter_bind_g_csm' env f_csm f_prd g_csm)


(*** Soundness *)

#push-options "--ifuel 0 --fuel 0"

let sound_repr_M_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd {lcsub_at_leaves lc})
  : prop
  = sound_M_of_LV lc (repr_M_of_LV lc)

let intro_sound_M_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
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

let rew_append_var_inj (#t0 #t1 : vprop_list) (x0 x1 : sl_f t0) (y0 y1 : sl_f t1)
  : squash ((append_vars x0 y0 == append_vars x1 y1) <==> (x0 == x1 /\ y0 == y1))
  = Fl.append_splitAt_ty _ _ x0 y0; Fl.append_splitAt_ty _ _ x1 y1

let rew_append_var_inj'
    #tx0 (x0 : sl_f tx0) #tx1 (x1 : sl_f tx1)
    #ty0 (y0 : sl_f ty0) #ty1 (y1 : sl_f ty1)
    #teq (_ : squash (tx0 == tx1 /\ ty0 == ty1 /\ teq == L.(tx0 @ ty0)))
  : squash (eq2 #(sl_f teq) (append_vars #tx0 #ty0 x0 y0) (append_vars #tx1 #ty1 x1 y1)
        <==> (x0 == x1 /\ y0 == y1))
  = rew_append_var_inj x0 x1 y0 y1

let rew_forall_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((forall (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)
  =
    introduce (forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) ==>
              (forall (sl : sl_f L.(v0 @ v1)) . p0 sl)
      with _ . introduce forall sl . _
      with (let sl0, sl1 = split_vars v0 v1 sl in
            Ll.pat_append ();
            FStar.Classical.forall_intro (Fl.splitAt_ty_append (vprop_list_sels_t v0) (vprop_list_sels_t v1));
            assert (sl == append_vars sl0 sl1);
            eliminate forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1) with sl0 sl1);
    introduce (forall (sl : sl_f L.(v0 @ v1)) . p0 sl) ==>
              (forall (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1))
      with _ . introduce forall sl0 sl1 . _
      with eliminate forall (sl : sl_f L.(v0 @ v1)) . p0 sl with (append_vars sl0 sl1)

let rew_exists_sl_f_app (v0 v1 : vprop_list) (p0 : sl_f L.(v0 @ v1) -> Type) (p1 : Type)
    (_ : squash ((exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) <==> p1))
  : squash ((exists (sl : sl_f L.(v0 @ v1)) . p0 sl) <==> p1)
  =
    introduce (exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)) ==>
              (exists (sl : sl_f L.(v0 @ v1)) . p0 sl)
      with _ . eliminate exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)
      returns _
      with _ . introduce exists (sl : sl_f L.(v0 @ v1)) . p0 sl
        with (append_vars sl0 sl1) and ();
    introduce (exists (sl : sl_f L.(v0 @ v1)) . p0 sl) ==>
              (exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1))
      with _ . eliminate exists (sl : sl_f L.(v0 @ v1)) . p0 sl
      returns _
      with _ . (
         let sl0, sl1 = split_vars v0 v1 sl in
         Ll.pat_append ();
         FStar.Classical.forall_intro (Fl.splitAt_ty_append (vprop_list_sels_t v0) (vprop_list_sels_t v1));
         assert (sl == append_vars sl0 sl1);
         introduce exists (sl0 : sl_f v0) (sl1 : sl_f v1) . p0 (append_vars sl0 sl1)
           with sl0 sl1 and ())

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

let norm_sound_LV2M () : Tac unit =
  norm [delta_only [`%repr_M_of_LV; `%repr_M_of_LV__tcs; `%repr_M_of_LV__tcs_sub;
                    `%M.tree_req; `%M.spec_req; `%M.return_req; `%M.bind_req;
                    `%M.tree_ens; `%M.spec_ens; `%M.return_ens; `%M.bind_ens;
                    `%Veq.vequiv_of_perm; `%Veq.vequiv_refl;
                    `%Veq.Mkvequiv?.veq_req; `%Veq.Mkvequiv?.veq_ens; `%Veq.Mkvequiv?.veq_eq; `%Veq.veq_ens1;
                    `%tree_req; `%tree_ens;
                    `%res_env_app; `%res_env_f; `%res_env; `%sub_prd_sl];
        delta_attr [`%Learn.Tactics.Util.__tac_helper__];
        iota; zeta]

let tac_sound_LV2M () : Tac unit =
  norm_sound_LV2M ();
  apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
  l_to_r [`extract_eij_framed_equiv];
  apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm []


#push-options "--ifuel 0 --fuel 1"

let sound_repr_M_of_LV__LCspec
      (env : vprop_list)
      (a : Type u#a) (sp : M.spec_r a -> Type u#(max a 2))
      (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sh : sp (M.Mkspec_r pre post req ens))
      (csm_f : eq_injection_l pre env)
  : squash (sound_repr_M_of_LV (LCspec env #a #sp (M.Mkspec_r pre post req ens) sh csm_f))
  =
    intro_sound_M_of_LV _ _
      (fun sl0 ->
        let sl0_0 = eij_sl #pre #env (L.index csm_f) sl0          in
        let sl0_1 = filter_sl (mask_not (eij_trg_mask csm_f)) sl0 in
        U.assert_by_tac (fun () ->
              tac_sound_LV2M ();
              // We rewrite [forall sl' . sl' = sl0_i ==> p sl'] into [p sl0_i]
              TLogic.(
                apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_0));
                  norm_sound_LV2M (); smt (); norm [simplify];
                apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_1));
                  smt (); norm [simplify]
              );
              trivial ()))
      (fun sl0 x sl1 sl_rem ->
        _ by (tac_sound_LV2M ();
              smt ()))

let sound_repr_M_of_LV__LCret
      (env : vprop_list)
      (a : Type u#a) (x : a) (sl_hint : M.post_t a)
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
      (a : Type u#a) (b : Type u#a) (f : M.prog_tree a) (g : (a -> M.prog_tree b))
      (f_csm : csm_t env) (f_prd : prd_t a)
      (cf : lin_cond env f f_csm f_prd)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
      (cg : ((x : a) ->
        lin_cond (res_env env f_csm (f_prd x)) (g x) (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd))

      (_ : squash (lcsub_at_leaves (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg)))
      (h_f : squash (sound_repr_M_of_LV cf))
      (h_g : (x : a) -> squash (sound_repr_M_of_LV (cg x)))
  : squash (sound_repr_M_of_LV (LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg))
  =
    introduce forall (x : a) .
            res_env_f env (bind_csm env f_csm g_csm) g_prd
         == res_env_f (res_env env f_csm (f_prd x)) (bind_g_csm' env f_csm (f_prd x) g_csm) g_prd
      with bind_g_csm'_res_env_f env b f_csm (f_prd x) g_csm g_prd;
    introduce forall (x : a) .
            filter_mask (mask_not (bind_g_csm' env f_csm (f_prd x) g_csm)) (res_env env f_csm (f_prd x))
         == filter_mask (mask_not (bind_csm env f_csm g_csm)) env
      with filter_bind_g_csm' env f_csm (f_prd x) g_csm;
    let h_g_req x sl0
      : squash (M.tree_req (g x) #_ #(res_env_f env (bind_csm env f_csm g_csm) g_prd) (repr_M_of_LV (cg x)) sl0
             <==> tree_req (cg x) sl0)
      = sound_M_of_LV_req (h_g x) sl0
    in let h_g_ens x (sl0 : sl_f (res_env env f_csm (f_prd x))) y sl1 sl_rem
      : squash (M.tree_ens (g x)
                  #_ #(res_env_f env (bind_csm env f_csm g_csm) g_prd) (repr_M_of_LV (cg x))
                  sl0 y (res_env_app sl1 sl_rem)
            <==> (tree_ens (cg x) sl0 y sl1 /\
                sl_rem == filter_sl (mask_not (bind_g_csm' env f_csm (f_prd x) g_csm)) sl0))
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
      (a : Type u#a) (b : Type u#a) (wp : pure_wp a) (g : a -> M.prog_tree b)
      (csm : csm_t env) (prd : prd_t b)
      (cg : (x : a) -> lin_cond env (g x) csm prd)

      (_ : squash (lcsub_at_leaves (LCbindP env #a #b #wp #g csm prd cg)))
      (h_g : (x : a) -> squash (sound_repr_M_of_LV (cg x)))
  : squash (sound_repr_M_of_LV (LCbindP env #a #b #wp #g csm prd cg))
  =
    FStar.Classical.forall_intro_squash_gtot h_g;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    intro_sound_M_of_LV _ _ (fun sl0 -> ()) (fun sl0 y sl2 sl_rem -> ())

#pop-options

// FIXME: without `--ide_id_info_off` the interactive mode takes a lot of time
#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"
let sound_repr_M_of_LV__LCsub_LCspec
      (env : vprop_list)
      (a : Type u#a) (sp : M.spec_r a -> Type u#(max a 2))
      (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sh : sp (M.Mkspec_r pre post req ens))
      (csm_f : eq_injection_l pre env)
      (csm1 : csm_t (filter_mask (mask_not (eij_trg_mask csm_f)) env))
      (prd1 : prd_t a)
      (prd_f1 : (x : a) -> Perm.pequiv_list (sub_prd env (eij_trg_mask csm_f) (post x) csm1) (prd1 x))
  : (let lc = LCsub env (eij_trg_mask csm_f) post
                    (LCspec env #a #sp (M.Mkspec_r pre post req ens) sh csm_f)
                    csm1 prd1 prd_f1
     in squash (lcsub_at_leaves lc /\ sound_repr_M_of_LV lc))
  = introduce _ /\ _
    with _ by (norm [delta_only [`%lcsub_at_leaves]; iota; zeta]; trivial ())
    and intro_sound_M_of_LV _ _
      (fun sl0 ->
        let sl0_0 = eij_sl #pre #env (L.index csm_f) sl0          in
        let sl0_1 = filter_sl (mask_not (eij_trg_mask csm_f)) sl0 in
        U.assert_by_tac (fun () ->
              tac_sound_LV2M ();
              TLogic.(
                apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_0));
                  norm_sound_LV2M (); smt (); norm [simplify];
                apply (`rew_iff_left); apply_raw (`rew_forall_eq (`@sl0_1));
                  smt (); norm [simplify]
              );
              trivial ()))
      (fun sl0 x sl1 sl_rem ->
        // A guard generated by [extract_sub_prd_framed_equiv]
        let gd : squash (prd1 x == Perm.apply_perm_r (Perm.perm_f_of_list (prd_f1 x))
                                                     (sub_prd env (eij_trg_mask csm_f) (post x) csm1))
              = ()
        in
        _ by (with_policy Goal (fun () ->
              norm_sound_LV2M ();
              apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [simplify];
              l_to_r [`extract_eij_framed_equiv];
              apply (`TLogic.rew_iff_left); rew_iff_LV2M (); norm [];
              l_to_r [`extract_sub_prd_framed_equiv]);
                later (); let _ = mintros () in exact (``@gd);
              apply (`TLogic.rew_iff_left); rew_iff_LV2M ();
                // additional goal generated by [rew_append_var_inj']
                seq explode (fun () -> try trefl () with | _ -> ());
                apply_lemma (`filter_bind_csm);
              l_to_r [`filter_sl_bind_csm];
              smt ()))
#pop-options


#push-options "--ifuel 0 --fuel 1"
let rec repr_M_of_LV_sound
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd {lcsub_at_leaves lc})
  : Lemma (ensures sound_M_of_LV lc (repr_M_of_LV lc)) (decreases lc)
  = match_lin_cond lc
      (fun a t csm prd lc -> squash (lcsub_at_leaves lc) ->
         squash (sound_M_of_LV lc (repr_M_of_LV lc)))
    begin fun (*LCspec*) a sp s sh csm_f -> fun _ ->
      let M.Mkspec_r pre post req ens = s in
      sound_repr_M_of_LV__LCspec env a sp pre post req ens sh csm_f
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
    begin fun (*LCsub*)  a0 f0 csm0 prd0 cf csm1 prd1 prd_f1 -> fun _ ->
      match_lin_cond cf
        (fun a f csm0 prd0 cf ->
           (csm1   : csm_t (filter_mask (mask_not csm0) env)) -> (prd1 : prd_t a) ->
           (prd_f1 : ((x : a) -> Perm.pequiv_list (sub_prd env csm0 (prd0 x) csm1) (prd1 x))) ->
           (let lc = LCsub env #a #f csm0 prd0 cf csm1 prd1 prd_f1 in
            squash (lcsub_at_leaves lc) ->
            squash (sound_M_of_LV lc (repr_M_of_LV lc))))
      begin fun (*LCspec*) a sp s sh csm_f -> fun csm1 prd1 prd_f1 _ ->
        let M.Mkspec_r pre post req ens = s in
        sound_repr_M_of_LV__LCsub_LCspec env a sp pre post req ens sh csm_f csm1 prd1 prd_f1
      end
      (fun (*LCret*)   a x sl_hint prd csm_f -> fun _ _ _ _ -> false_elim ())
      (fun (*LCbind*)  a b f g f_csm f_prd cf g_csm g_prd cg -> fun _ _ _ _ -> false_elim ())
      (fun (*LCbindP*) a b wp g csm prd cg -> fun _ _ _ _ -> false_elim ())
      (fun (*LCsub*)   a0 f0 csm0 prd0 cf csm1 prd1 prd_f1 -> fun _ _ _ _ -> false_elim ())
      csm1 prd1 prd_f1 ()
    end ()
#pop-options

#push-options "--ifuel 0 --fuel 1"
let repr_M_of_LV_top_sound
      (#a : Type u#a) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
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
