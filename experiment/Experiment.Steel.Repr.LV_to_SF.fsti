module Experiment.Steel.Repr.LV_to_SF

module L  = FStar.List.Pure
module M  = Experiment.Steel.Repr.M
module SF = Experiment.Steel.Repr.SF
module Fl = Learn.FList

open Experiment.Steel.VPropList
open Experiment.Steel.Repr.LV

#set-options "--fuel 1 --ifuel 1"

[@@ strict_on_arguments [5]] (* strict on [lc] *)
let rec repr_SF_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
      (sl0 : sl_f env)
  : Tot (SF.prog_tree a (M.post_sl_t prd)) (decreases lc)
  = match lc with
  | LCspec env #a #sp s sh csm_f ->
      let sl0' = eij_sl (L.index csm_f) sl0 in
      SF.Tspec a (M.post_sl_t s.spc_post) (s.spc_req sl0') (s.spc_ens sl0')
  | LCret  env #a #x prd csm_f ->
      SF.Tret a x (M.post_sl_t prd) (Fl.dlist_of_f (eij_sl (L.index csm_f) sl0))
  | LCbind env #a #b f_csm f_prd cf g_csm g_prd cg ->
      SF.Tbind a b (M.post_sl_t f_prd) (M.post_sl_t g_prd)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (f_prd x)) ->
                  repr_SF_of_LV (cg x) (res_sel sl0 f_csm sl1))
  | LCbindP env #a #b #wp #g csm prd cg ->
      SF.TbindP a b (M.post_sl_t prd) wp (fun (x : a) -> repr_SF_of_LV (cg x) sl0)
  | LCsub  env csm0 prd0 cf csm1 prd1 prd_f ->
      SF.Tbind a a (M.post_sl_t prd0) (M.post_sl_t prd1)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (prd0 x)) ->
                  let sl1' : sl_f (prd1 x) = sub_prd_sl #env sl0 csm0 sl1 csm1 (prd_f x) in
                  SF.Tret a x (M.post_sl_t prd1) (Fl.dlist_of_f sl1'))


(*** Soundness *)

let sound_SF_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
      (sl0 : sl_f env)
      (sf : SF.prog_tree a (M.post_sl_t prd))
  : prop
  =
    (tree_req lc sl0 <==> SF.tree_req sf) /\
    (forall (res : a) (sl1 : sl_f (prd res)) .
       tree_ens lc sl0 res sl1 <==> SF.tree_ens sf res sl1)

val repr_SF_of_LV_sound
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
      (sl0 : sl_f env)
  : Lemma (sound_SF_of_LV lc sl0 (repr_SF_of_LV lc sl0))
