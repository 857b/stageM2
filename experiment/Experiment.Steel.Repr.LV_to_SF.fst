module Experiment.Steel.Repr.LV_to_SF

module U = Learn.Util

open FStar.Tactics

#set-options "--fuel 1 --ifuel 1"

let normal_SF_of_LV : list norm_step =
  [delta_only [`%repr_SF_of_LV; `%sound_SF_of_LV;
              `%tree_req; `%tree_ens;
              `%SF.tree_req; `%SF.tree_ens];
   iota; zeta; simplify]

#push-options "--ifuel 0 --fuel 0"
let rec repr_SF_of_LV_sound
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
      (sl0 : sl_f env)
  : Lemma (ensures sound_SF_of_LV lc sl0 (repr_SF_of_LV lc sl0)) (decreases lc)
  = match_lin_cond lc
      (fun a t csm prd lc -> (sl0 : sl_f env) ->
           squash (Pervasives.norm normal_SF_of_LV (sound_SF_of_LV lc sl0 (repr_SF_of_LV lc sl0))))
    (fun (*LCspec*) a sp s sh csm_f -> fun sl0 -> ())
    (fun (*LCret*)  a x sl_hint prd csm_f -> fun sl0 -> ())
    begin fun (*LCbind*) a b f g f_csm f_prd cf g_csm g_prd cg -> fun sl0 ->
      repr_SF_of_LV_sound cf sl0;
      introduce forall (x : a) (sl1 : sl_f (f_prd x)) .
          let sl1' = res_sel sl0 f_csm sl1 in
          sound_SF_of_LV (cg x) sl1' (repr_SF_of_LV (cg x) sl1')
        with repr_SF_of_LV_sound (cg x) (res_sel sl0 f_csm sl1)
    end
    begin fun (*LCbindP*) a b wp g csm prd cg -> fun sl0 ->
      FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
      introduce forall (x : a) . sound_SF_of_LV (cg x) sl0 (repr_SF_of_LV (cg x) sl0)
        with repr_SF_of_LV_sound (cg x) sl0
    end
    begin fun (*LCsub*)  a f csm0 prd0 cf csm1 prd1 prd_f1 -> fun sl0 ->
      repr_SF_of_LV_sound cf sl0
    end sl0
#pop-options
