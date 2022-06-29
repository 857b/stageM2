module Experiment.Steel.Repr.LV_to_SF

module U    = Learn.Util
module L    = FStar.List.Pure
module T    = FStar.Tactics
module Ll   = Learn.List
module M    = Experiment.Steel.Repr.M
module SF   = Experiment.Steel.Repr.SF
module Fl   = Learn.FList
module Dl   = Learn.DList
module Msk  = Learn.List.Mask
module Perm = Learn.Permutation

open Experiment.Steel.VPropList
open Experiment.Steel.Repr.LV

#set-options "--fuel 1 --ifuel 1"

irreducible let __LV2SF__ : unit = ()

[@@ __LV2SF__]
let rec len_eff (#a : Type) (l : list a) : (n : nat { n == L.length l }) =
  match l with
  | [] -> 0
  | _ :: l -> 1 + len_eff l

[@@ __LV2SF__]
let rec index_eff (#a : Type) (l : list a) (i : Ll.dom l) : (x : a { x == L.index l i }) =
  let hd :: tl = l in
  if i = 0 then hd else index_eff tl (i-1)

[@@ __LV2SF__]
let eij_sl_eff (#src #trg : vprop_list) (eij : eq_injection_l src trg) (xs : sl_f trg)
  : (sl : sl_f src { sl == eij_sl (L.index eij) xs })
  =
    let sl = Fl.mk_flist (vprop_list_sels_t src) (fun i -> xs (index_eff eij i) <: (L.index src i).t) in
    (**) Fl.flist_extensionality sl (eij_sl (L.index eij) xs) (fun i -> ());
    sl

[@@ __LV2SF__]
let split_vars_eff (v0 v1 : vprop_list) (sl : sl_f L.(v0 @ v1))
  : (sls : (sl_f v0 & sl_f v1) { sls == split_vars v0 v1 sl })
  =
    let n = len_eff v0 in
    (**) Ll.pat_append ();
    let sl0 = Fl.mk_flist (vprop_list_sels_t v0) (fun i -> sl i       <: (L.index v0 i).t) in
    let sl1 = Fl.mk_flist (vprop_list_sels_t v1) (fun i -> sl (n + i) <: (L.index v1 i).t) in
    (**) Fl.flist_extensionality sl0 (split_vars v0 v1 sl)._1 (fun i -> ());
    (**) Fl.flist_extensionality sl1 (split_vars v0 v1 sl)._2 (fun i -> ());
    (sl0, sl1)

[@@ __LV2SF__]
let append_vars_eff (#v0 #v1 : vprop_list) (sl0 : sl_f v0) (sl1 : sl_f v1)
  : (sl : sl_f L.(v0 @ v1) { sl == append_vars sl0 sl1 })
  =
    let n = len_eff v0 in
    (**) Ll.pat_append ();
    let sl : sl_f L.(v0 @ v1) = Fl.mk_flist L.(vprop_list_sels_t L.(v0 @ v1)) (fun i ->
      if i < n
      then (sl0 i <: (L.(index (v0 @ v1) i)).t)
      else (sl1 (i - n) <: (L.(index (v0 @ v1) i)).t))
    in
    (**) Fl.flist_extensionality sl (append_vars sl0 sl1) (fun i -> ());
    sl

[@@ __LV2SF__]
let res_sel_eff (#env : vprop_list) (sl0 : sl_f env) (csm : csm_t env) (#prd : vprop_list) (sl1 : sl_f prd)
  : (sl : (sl_f (res_env env csm prd)) { sl == res_sel sl0 csm sl1})
  = append_vars_eff sl1 (filter_sl (Msk.mask_not csm) sl0)

#push-options "--fuel 0 --ifuel 0"
(**) private val __begin_opt_0 : unit
[@@ __LV2SF__]
let sub_prd_sl_eff
      (#env : vprop_list) (sl0 : sl_f env)
      (csm  : csm_t env)  (#prd : vprop_list) (sl1 : sl_f prd)
      (csm' : csm_t Msk.(filter_mask (mask_not csm) env))
      (#prd' : vprop_list) (prd_f : Perm.pequiv_list (sub_prd env csm prd csm') prd')
  : (sl : sl_f prd' { sl == sub_prd_sl sl0 csm sl1 csm' prd_f })
  =
    let sl_sprd = append_vars_eff sl1 Msk.(filter_sl csm' (filter_sl (mask_not csm) sl0)) in
    let sl_prd' = Fl.mk_flist (vprop_list_sels_t prd') (fun i ->
                        sl_sprd (index_eff prd_f i) <: (L.index prd' i).t)                in
    (**) Fl.flist_extensionality sl_prd' (sub_prd_sl sl0 csm sl1 csm' prd_f) (fun i -> ());
    sl_prd'
#pop-options
(**) private val __end_opt_0 : unit

[@@ __LV2SF__]
let dlist_of_sl_eff (#v : vprop_list) (sl : sl_f v)
  : (sl' : Dl.dlist (vprop_list_sels_t v) { sl' == Fl.dlist_of_f sl })
  =
    let f_ty (i : Ll.dom v) : Type = (index_eff v i).t in
    (**) Ll.list_extensionality (Ll.initi 0 (len_eff v) f_ty) (vprop_list_sels_t v) (fun i -> ());
    let sl' : Dl.dlist (vprop_list_sels_t v) = Dl.initi 0 (len_eff v) f_ty sl in
    (**) Dl.dlist_extensionality sl' (Fl.dlist_of_f sl) (fun i -> ());
    sl'


[@@ __LV2SF__; strict_on_arguments [5]] (* strict on [lc] *)
let rec repr_SF_of_LV
      (#env : vprop_list) (#a : Type u#a) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond env t csm prd)
      (sl0 : sl_f env)
  : Tot (SF.prog_tree a (M.post_sl_t prd)) (decreases lc)
  = match lc with
  | LCspec env #a #sp s sh pre_f ->
      let sl0s = split_vars_eff s.spc_pre s.spc_ro (eij_sl_eff pre_f sl0) in
      SF.Tspec a (M.post_sl_t s.spc_post) (s.spc_req sl0s._1 sl0s._2) (fun x sl1 -> s.spc_ens sl0s._1 x sl1 sl0s._2)
  | LCret  env #a #x prd csm_f ->
      SF.Tret a x (M.post_sl_t prd) (dlist_of_sl_eff (eij_sl_eff csm_f sl0))
  | LCbind env #a #b f_csm f_prd cf g_csm g_prd cg ->
      SF.Tbind a b (M.post_sl_t f_prd) (M.post_sl_t g_prd)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (f_prd x)) ->
                  repr_SF_of_LV (cg x) (res_sel_eff sl0 f_csm sl1))
  | LCbindP env #a #b #wp #g csm prd cg ->
      SF.TbindP a b (M.post_sl_t prd) wp (fun (x : a) -> repr_SF_of_LV (cg x) sl0)
  | LCif    env #a #guard #thn #els csm prd cthn cels ->
      SF.Tif   a guard (M.post_sl_t prd)
               (repr_SF_of_LV cthn sl0)
               (repr_SF_of_LV cels sl0)
  | LCsub  env csm0 prd0 cf csm1 prd1 prd_f ->
      SF.Tbind a a (M.post_sl_t prd0) (M.post_sl_t prd1)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (prd0 x)) ->
                  let sl1' : sl_f (prd1 x) = sub_prd_sl_eff #env sl0 csm0 sl1 csm1 (prd_f x) in
                  SF.Tret a x (M.post_sl_t prd1) (dlist_of_sl_eff sl1'))


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
