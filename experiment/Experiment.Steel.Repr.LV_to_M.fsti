module Experiment.Steel.Repr.LV_to_M

module U    = Learn.Util
module L    = FStar.List.Pure
module M    = Experiment.Steel.Repr.M
module Ll   = Learn.List
module Fl   = Learn.FList
module Veq  = Experiment.Steel.VEquiv
module Perm = Learn.Permutation

open Learn.List.Mask
open Experiment.Steel.VPropList
open Experiment.Steel.Repr.LV


let res_env_f (env : vprop_list) (#a : Type) (csm : csm_t env) (prd : prd_t a) (x : a)
  : vprop_list
  = res_env env csm (prd x)


let typ_to_M
      (env : vprop_list)
      (#a : Type u#a) (t : M.prog_tree a)
      (csm : csm_t env) (prd : prd_t a)
  : Type
  = M.tree_cond t env (res_env_f env csm prd)

let lc_to_M
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
  : Type
  = typ_to_M env t csm prd


let eij_framed_equiv
      (env : vprop_list) (pre : M.pre_t) (csm_f : eq_injection_l pre env)
  : vequiv_perm env L.(pre @ filter_mask (mask_not (eij_trg_mask csm_f)) env)
  =
    let m = eij_trg_mask csm_f in
    Perm.(pequiv_trans
      (mask_pequiv_append m env)
      (pequiv_append (eij_equiv csm_f) (pequiv_refl (filter_mask (mask_not m) env))))

val extract_eij_framed_equiv
      (env : vprop_list) (pre : M.pre_t) (csm_f : eq_injection_l pre env)
      (sl : sl_f env)
  : Lemma (extract_vars (eij_framed_equiv env pre csm_f) sl
        == append_vars (eij_sl (L.index csm_f) sl)
                       (filter_sl (mask_not (eij_trg_mask csm_f)) sl))


let spec_post_equiv
      (env : vprop_list)
      (pre post ro : vprop_list)
      (pre_f : eq_injection_l L.(pre @ ro) env)
  : vequiv_perm L.((post @ ro) @ filter_mask (mask_not (eij_trg_mask pre_f)) env)
                  (res_env env (eij_trg_mask (eij_split pre ro pre_f)._1) post)
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
    L.(calc (==) {
      (post @ ro) @ filter_mask (mask_not m_trg) env;
    == { append_assoc post ro (filter_mask (mask_not m_trg) env) }
      post @ ro @ filter_mask (mask_not m_trg) env;
    == { eij_split1_trg_mask pre ro pre_f }
      post @ ro @ filter_mask (mask_not (mask_comp_or m_trg0 m_trg1)) env;
    == { mask_not_comp_or m_trg0 m_trg1;
         filter_mask_and (mask_not m_trg0) (mask_not m_trg1) env }
      post @ (ro @ flt1);
    });
    assert L.(res_env env (eij_trg_mask (eij_split pre ro pre_f)._1) post == post @ env1);
    
    let f0 : vequiv_perm ro flt0
      = Perm.pequiv_sym (eij_equiv ro_f1)  in
    let f1 : vequiv_perm L.(flt0 @ flt1) env1
      = mask_pequiv_append' m_trg1 env1    in
    let f2 : vequiv_perm L.(post @ (ro @ flt1)) L.(post @ env1)
      = Perm.pequiv_append (Perm.pequiv_refl post)
          (Perm.pequiv_trans
            (Perm.pequiv_append f0 (Perm.pequiv_refl flt1))
            f1)
    in
    U.cast _ f2

val extract_spec_post_equiv
      (env : vprop_list) (pre post ro : vprop_list) (pre_f : eq_injection_l L.(pre @ ro) env)
      (sl0 : sl_f env) (sl_post : sl_f post)
  : Lemma (extract_vars (spec_post_equiv env pre post ro pre_f)
                        (append_vars (append_vars sl_post (split_vars pre ro (eij_sl (L.index pre_f) sl0))._2)
                                     (filter_sl (mask_not (eij_trg_mask pre_f)) sl0))
        == append_vars sl_post (filter_sl (mask_not (eij_trg_mask (eij_split pre ro pre_f)._1)) sl0))


let repr_M_of_LV__tcs
      (env : vprop_list)
      (a : Type u#a) (s : M.spec_r a)
      (pre_f : eq_injection_l (M.spc_pre1 s) env)
  : M.tree_cond_Spec a (M.spc_pre1 s) (M.spc_post1 s)
  = {
    tcs_pre     = env;
    tcs_post    = res_env_f env (spec_csm pre_f) s.spc_post;
    tcs_frame   = filter_mask (mask_not (eij_trg_mask pre_f)) env;
    tcs_pre_eq  = Veq.vequiv_of_perm (eij_framed_equiv env (M.spc_pre1 s) pre_f);
    tcs_post_eq = (fun x -> Veq.vequiv_of_perm (spec_post_equiv env s.spc_pre (s.spc_post x) s.spc_ro pre_f));
  }

#push-options "--ifuel 0 --fuel 0"
let sub_prd_framed_equiv
      (env  : vprop_list)
      (csm0 : csm_t env) (prd0 : vprop_list)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : vprop_list)
      (veq  : vequiv_perm (sub_prd env csm0 prd0 csm1) prd1)
  : vequiv_perm L.(prd0 @ filter_mask (mask_not csm0) env)
                (res_env env (bind_csm env csm0 csm1) prd1)
  =
    let env1 = filter_mask (mask_not csm0) env  in
    let flt1 = filter_mask csm1 env1            in
    let flt2 = filter_mask (mask_not csm1) env1 in
    assert (sub_prd env csm0 prd0 csm1 == L.(prd0 @ flt1));
    calc (==) {
      res_env env (bind_csm env csm0 csm1) prd1;
    == { }
      L.(prd1 @ filter_mask (mask_not (bind_csm env csm0 csm1)) env);
    == { filter_bind_csm env csm0 csm1 }
      L.(prd1 @ flt2);
    };
    let f0  : vequiv_perm L.(prd0 @ flt1) prd1 = U.cast _ veq in
    L.append_assoc prd0 flt1 flt2;
    let f0' : vequiv_perm L.(prd0 @ flt1 @ flt2) L.(prd1 @ flt2)
      = U.cast _ (Perm.pequiv_append f0 (Perm.pequiv_refl flt2))
    in
    let f1  : vequiv_perm env1 L.(flt1 @ flt2)
       = mask_pequiv_append csm1 env1 in
    let f1' : vequiv_perm L.(prd0 @ env1) L.(prd0 @ flt1 @ flt2)
      = Perm.pequiv_append (Perm.pequiv_refl prd0) f1
    in
    Perm.pequiv_trans f1' f0'
#pop-options

val extract_sub_prd_framed_equiv
      (env : vprop_list) 
      (csm0 : csm_t env) (prd0 : vprop_list)
      (csm1 : csm_t (filter_mask (mask_not csm0) env)) (prd1 : vprop_list)
      (veq  : vequiv_perm (sub_prd env csm0 prd0 csm1) prd1)
      (sl0 : sl_f prd0) (sl1 : sl_f (filter_mask (mask_not csm0) env))
  : Lemma (filter_bind_csm env csm0 csm1;
       extract_vars (sub_prd_framed_equiv env csm0 prd0 csm1 prd1 veq) (append_vars sl0 sl1)
    == append_vars (extract_vars veq (append_vars sl0 (filter_sl csm1 sl1)))
                   (filter_sl (mask_not csm1) sl1))

let spec_sub_post_equiv
      (env : vprop_list) (#a : Type) (s : M.spec_r a) (pre_f : eq_injection_l (M.spc_pre1 s) env)
      (csm1 : csm_t (filter_mask (mask_not (spec_csm pre_f)) env)) (prd1 : prd_t a)
      (prd_f1 : (x : a) -> Perm.pequiv_list (sub_prd env (spec_csm pre_f) (s.spc_post x) csm1) (prd1 x))
      (x : a)
  : vequiv_perm L.(M.spc_post1 s x @ filter_mask (mask_not (eij_trg_mask pre_f)) env)
                  (res_env env (bind_csm env (spec_csm pre_f) csm1) (prd1 x))
  = Perm.pequiv_trans (spec_post_equiv env s.spc_pre (s.spc_post x) s.spc_ro pre_f)
                      (sub_prd_framed_equiv env (spec_csm pre_f) (s.spc_post x)
                                            csm1 (prd1 x) (Perm.perm_f_of_list (prd_f1 x)))

let repr_M_of_LV__tcs_sub
      (env : vprop_list)
      (a : Type u#a) (s : M.spec_r a)
      (pre_f : eq_injection_l (M.spc_pre1 s) env)
      (csm1 : csm_t (filter_mask (mask_not (spec_csm pre_f)) env)) (prd1 : prd_t a)
      (prd_f1 : (x : a) -> Perm.pequiv_list (sub_prd env (spec_csm pre_f) (s.spc_post x) csm1) (prd1 x))
  : M.tree_cond_Spec a (M.spc_pre1 s) (M.spc_post1 s)
  = {
    tcs_pre     = env;
    tcs_post    = res_env_f env (bind_csm env (spec_csm pre_f) csm1) prd1;
    tcs_frame   = filter_mask (mask_not (eij_trg_mask pre_f)) env;
    tcs_pre_eq  = Veq.vequiv_of_perm (eij_framed_equiv env (M.spc_pre1 s) pre_f);
    tcs_post_eq = (fun x -> Veq.vequiv_of_perm (spec_sub_post_equiv env s pre_f csm1 prd1 prd_f1 x))
  }

val bind_g_csm'_res_env_f
      (env : vprop_list) (b : Type)
      (f_csm : csm_t env) (f_prd : vprop_list)
      (g_csm : csm_t (filter_mask (mask_not f_csm) env)) (g_prd : prd_t b)
  : Lemma (res_env_f (res_env env f_csm f_prd) (bind_g_csm' env f_csm f_prd g_csm) g_prd
        == res_env_f env (bind_csm env f_csm g_csm) g_prd)


#push-options "--ifuel 1 --fuel 2 --z3rlimit 30"
[@@ strict_on_arguments [5]] (* strict on [lc] *)
inline_for_extraction
let rec repr_M_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
  : Pure (lc_to_M lc) (requires lcsub_at_leaves lc) (ensures fun _ -> True) (decreases lc)
  = match lc with
  | LCspec env #a #sp s sh pre_f ->
      M.TCspec #a #sp s sh  (repr_M_of_LV__tcs env a s pre_f)
  | LCret env #a #x #sl_hint prd csm_f ->
      M.TCret #a #x #sl_hint
          env (fun x' -> L.(prd x' @ filter_mask (mask_not (eij_trg_mask csm_f)) env))
          (Veq.vequiv_of_perm (eij_framed_equiv env (prd x) csm_f))
  | LCbind env #a #b #f #g f_csm f_prd cf g_csm g_prd cg ->
      M.TCbind #a #b #f #g env (res_env_f env f_csm f_prd) (res_env_f env (bind_csm env f_csm g_csm) g_prd)
          (repr_M_of_LV cf)
          (fun (x : a) ->
            (**) bind_g_csm'_res_env_f env b f_csm (f_prd x) g_csm g_prd;
            repr_M_of_LV (cg x))
  | LCbindP env #a #b #wp #g csm prd cg ->
      M.TCbindP #a #b #wp #g env (res_env_f env csm prd) (fun x -> repr_M_of_LV (cg x))
  | LCif  env #a #guard #thn #els cms prd cthn cels ->
      M.TCif #a #guard #thn #els env (res_env_f env csm prd)
          (repr_M_of_LV cthn)
          (repr_M_of_LV cels)
  | LCsub env #a0 #f0 csm0 prd0 cf csm1 prd1 prd_f1 ->
      let LCspec env #a #sp s sh pre_f = cf in
      let prd_f1 (x : a) : Perm.pequiv_list (sub_prd env (spec_csm pre_f) (s.spc_post x) csm1) (prd1 x)
            = U.cast _ (prd_f1 x)
      in
      M.TCspec #a #sp s sh (repr_M_of_LV__tcs_sub env a s pre_f csm1 prd1 prd_f1)
#pop-options

#push-options "--ifuel 0 --fuel 0"
inline_for_extraction
let repr_M_of_LV_top
      (#a : Type u#a) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
      (lc : top_lin_cond t pre post)
  : Pure (M.tree_cond t pre (U.eta post))
         (requires lcsub_at_leaves lc) (ensures fun _ -> True)
  =
    U.funext_eta (res_env_f pre (csm_all pre) post) (U.eta post)
                 (U.by_refl ()) (U.by_refl ())
      (fun x -> filter_mask_false (mask_not (csm_all pre)) pre (fun i -> ()));
    repr_M_of_LV lc
#pop-options

(*** Soundness *)

let res_env_split
      (#env : vprop_list) (#csm : csm_t env) (#prd : vprop_list)
      (sl : sl_f (res_env env csm prd))
  : sl_f prd & sl_f (filter_mask (mask_not csm) env)
  =
    split_vars prd (filter_mask (mask_not csm) env) sl

let res_env_app
      (#env : vprop_list) (#csm : csm_t env) (#prd : vprop_list)
      (sl1 : sl_f prd) (sl2 : sl_f (filter_mask (mask_not csm) env))
  : sl_f (res_env env csm prd)
  =
    append_vars sl1 sl2

let sound_M_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd) (mc : lc_to_M lc)
  : prop
  =
    forall (sl0 : sl_f env) .
      (M.tree_req t mc sl0 <==> tree_req lc sl0) /\
   (forall (res : a) (sl1 : sl_f (prd res)) (sl_rem : sl_f (filter_mask (mask_not csm) env)) .
      (M.tree_ens t mc sl0 res (res_env_app sl1 sl_rem) <==>
      (tree_ens lc sl0 res sl1 /\
       sl_rem == filter_sl (mask_not csm) sl0)))

val repr_M_of_LV_sound
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd {lcsub_at_leaves lc})
  : Lemma (sound_M_of_LV lc (repr_M_of_LV lc))

val repr_M_of_LV_top_sound
      (#a : Type u#a) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
      (lc : top_lin_cond t pre post {lcsub_at_leaves lc})
  : Lemma (let mc = repr_M_of_LV_top lc in
      forall (sl0 : sl_f pre) . (M.tree_req t mc sl0 <==> tree_req lc sl0)  /\
     (forall (x : a) (sl1 : sl_f (post x)) .
        M.tree_ens t mc sl0 x sl1 <==> tree_ens lc sl0 x sl1)
  )
