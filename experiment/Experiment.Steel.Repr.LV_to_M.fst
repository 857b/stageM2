module Experiment.Steel.Repr.LV_to_M

open FStar.Tactics

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
