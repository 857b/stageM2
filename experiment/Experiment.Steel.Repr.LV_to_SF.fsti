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

open Experiment.Steel.Interface
open Experiment.Steel.VPropList
open Experiment.Steel.Repr.LV

#set-options "--fuel 1 --ifuel 1"
(**) private val __begin_module : unit

(**** Efficient operations on sl_list *)

/// The following operations on [sl_list] (that is [Dl.dlist] of types of [vprop']) are equivalent to the operations
/// on [sl_f] (that is [Fl.flist]) used in the specifications. They are reduced in the phase LV2SF.

[@@ __LV2SF__]
let rec len_eff (#a : Type) (l : list a) : n : nat { n == L.length l } =
  match l with
  | [] -> 0
  | _ :: l -> 1 + len_eff l

[@@ __LV2SF__]
let rec index_eff (#a : Type) (l : list a) (i : Ll.dom l) : x : a { x == L.index l i } =
  let hd :: tl = l in
  if i = 0 then hd else index_eff tl (i-1)

[@@ __LV2SF__]
let dl_initi_vp (v : vprop_list) (f : (i : Ll.dom v) -> Tot (L.index v i).t)
  : sl_list v
  =
    let n = len_eff v in
    let f_ty (i : Ll.dom v) : Type = (index_eff v i).t in
    (**) Ll.list_extensionality (vprop_list_sels_t v) (Ll.initi 0 n f_ty) (fun _ -> ());
    Dl.initi 0 n f_ty f

[@@ __LV2SF__]
let sl_list_of_f (#v : vprop_list) (f : sl_f v)
  : l : sl_list v {l == Fl.dlist_of_f f}
  =
    let l = dl_initi_vp v f in
    (**) Dl.dlist_extensionality l (Fl.dlist_of_f f) (fun _ -> ());
    l

[@@ __LV2SF__]
let eij_sl_l (#src #trg : vprop_list) (eij : eq_injection_l src trg) (xs : sl_list trg)
  : sl : sl_list src { Fl.flist_of_d sl == eij_sl (L.index eij) (Fl.flist_of_d xs) }
  =
    let sl = dl_initi_vp src (fun i -> Dl.index xs (index_eff eij i) <: (L.index src i).t) in
    (**) Fl.flist_extensionality (Fl.flist_of_d sl) (eij_sl (L.index eij) (Fl.flist_of_d xs)) (fun i -> ());
    sl

[@@ __LV2SF__]
let split_vars_l (v0 v1 : vprop_list) (sl : sl_list L.(v0 @ v1))
  : sls : (sl_f v0 & sl_f v1) { sls == split_vars v0 v1 (Fl.flist_of_d sl) }
  =
    let n = len_eff v0 in
    (**) Ll.pat_append ();
    let sl0  = Fl.mk_flist (vprop_list_sels_t v0) (fun i -> Dl.index sl i       <: (L.index v0 i).t) in
    let sl1  = Fl.mk_flist (vprop_list_sels_t v1) (fun i -> Dl.index sl (n + i) <: (L.index v1 i).t) in
    let sls' = split_vars v0 v1 (Fl.flist_of_d sl) in
    (**) Fl.flist_extensionality sl0 sls'._1 (fun i -> ());
    (**) Fl.flist_extensionality sl1 sls'._2 (fun i -> ());
    (sl0, sl1)

[@@ __LV2SF__]
let append_vars_l (#v0 #v1 : vprop_list) (sl0 : sl_list v0) (sl1 : sl_list v1)
  : sl : sl_list L.(v0 @ v1) { Fl.flist_of_d sl == append_vars (Fl.flist_of_d sl0) (Fl.flist_of_d sl1) }
  =
    (**) Ll.pat_append ();
    let sl = Dl.append sl0 sl1 in
    (**) Fl.flist_extensionality (Fl.flist_of_d sl) (append_vars (Fl.flist_of_d sl0) (Fl.flist_of_d sl1))
    (**)   (fun i -> Dl.append_index sl0 sl1 i);
    sl

[@@ __LV2SF__]
let filter_sl_l (#vs : vprop_list) (mask : Msk.mask_t vs) (xs : sl_list vs)
  : sl : sl_list (Msk.filter_mask mask vs) { Fl.flist_of_d sl == filter_sl mask (Fl.flist_of_d xs) }
  =
    (**) Msk.filter_mask_f_dl_f mask _ (Fl.flist_of_d xs);
    Msk.filter_mask_dl mask _ xs

[@@ __LV2SF__]
let res_sel_l (#env : vprop_list) (sl0 : sl_list env) (csm : csm_t env) (#prd : vprop_list) (sl1 : sl_list prd)
  : sl : sl_list (res_env env csm prd) { Fl.flist_of_d sl == res_sel (Fl.flist_of_d sl0) csm (Fl.flist_of_d sl1)}
  =
    append_vars_l sl1 (filter_sl_l (Msk.mask_not csm) sl0)

[@@ __LV2SF__]
let extract_vars_l (#src #dst : vprop_list) (p : Perm.pequiv_list src dst) (xs : sl_list src)
  : ys : sl_list dst { Fl.flist_of_d ys == extract_vars (Perm.perm_f_of_list p) (Fl.flist_of_d xs) }
  =
    let ys = dl_initi_vp dst (fun i -> Dl.index xs (index_eff p i)) in
    (**) Fl.flist_extensionality (Fl.flist_of_d ys) (extract_vars (Perm.perm_f_of_list p) (Fl.flist_of_d xs))
    (**)   (fun i -> ());
    ys

[@@ __LV2SF__]
let sub_prd_sl_l
      (#env : vprop_list) (sl0 : sl_list env)
      (csm  : csm_t env)  (#prd : vprop_list) (sl1 : sl_list prd)
      (csm' : csm_t Msk.(filter_mask (mask_not csm) env))
      (#prd' : vprop_list) (prd_f : Perm.pequiv_list (sub_prd env csm prd csm') prd')
  : (sl : sl_list prd' { Fl.flist_of_d sl == sub_prd_sl (Fl.flist_of_d sl0) csm (Fl.flist_of_d sl1) csm' prd_f })
  =
    extract_vars_l prd_f (append_vars_l sl1 Msk.(filter_sl_l csm' (filter_sl_l (mask_not csm) sl0)))

#push-options "--ifuel 0 --fuel 0"
(**) private val __begin_opt_0 : unit
[@@ __LV2SF__]
let append_vars_mask_l
      (#vs : vprop_list) (m : Msk.mask_t vs)
      (sl0 : sl_list Msk.(filter_mask m vs)) (sl1 : sl_list Msk.(filter_mask (mask_not m) vs))
  : sl : sl_list vs { Fl.flist_of_d sl == append_vars_mask m (Fl.flist_of_d sl0) (Fl.flist_of_d sl1) }
  =
    let sl : sl_list vs = Msk.dl_append_on_mask m sl0 sl1 in
    Fl.flist_extensionality (Fl.flist_of_d sl) (append_vars_mask m (Fl.flist_of_d sl0) (Fl.flist_of_d sl1))
      (fun i -> Msk.dl_append_on_mask_index m sl0 sl1 i;
             Msk.mask_perm_append'_index m i);
    sl
#pop-options
(**) private val __begin_opt_1 : unit


(*** [repr_SF_of_LV] *)

[@@ __LV2SF__; strict_on_arguments [5]] (* strict on [lc] *)
let rec repr_SF_of_LV
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond u#a u#p env t csm prd)
      (sl0 : sl_list env)
  : Tot (SF.prog_tree u#a u#0 u#p a (M.post_sl_t prd)) (decreases lc)
  = match lc with
  | LCspec env #a #sp s sh pre_f ->
      let sl0s = split_vars_l s.spc_pre s.spc_ro (eij_sl_l pre_f sl0) in
      SF.Tspec a (M.post_sl_t s.spc_post) (s.spc_req sl0s._1 sl0s._2) (fun x sl1 -> s.spc_ens sl0s._1 x sl1 sl0s._2)
  | LCret  env #a #x prd csm_f ->
      SF.Tret a x (M.post_sl_t prd) (eij_sl_l csm_f sl0)
  | LCbind env #a #b f_csm f_prd cf g_csm g_prd cg ->
      SF.Tbind a b (M.post_sl_t f_prd) (M.post_sl_t g_prd)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (f_prd x)) ->
                  repr_SF_of_LV (cg x) (res_sel_l sl0 f_csm (sl_list_of_f sl1)))
  | LCbindP env #a #b #wp #g csm prd cg ->
      SF.TbindP a b (M.post_sl_t prd) wp (fun (x : a) -> repr_SF_of_LV (cg x) sl0)
  | LCif    env #a #guard #thn #els csm prd cthn cels ->
      SF.Tif   a guard (M.post_sl_t prd)
               (repr_SF_of_LV cthn sl0)
               (repr_SF_of_LV cels sl0)
  | LCgen env #a #sp {lcg_s = s; lcg_sf = sf} pre_f ->
      // We explicit [M.spc_pre1 s], otherwise it would have been inferred to [M.spc_pre1 (...).lcg_s]
      let sl0s = split_vars_l s.spc_pre s.spc_ro (extract_vars_l #env #(M.spc_pre1 s) pre_f sl0) in
      sf sl0s._1 sl0s._2
  | LCsub  env csm0 prd0 cf csm1 prd1 prd_f ->
      SF.Tbind a a (M.post_sl_t prd0) (M.post_sl_t prd1)
               (repr_SF_of_LV cf sl0)
               (fun (x : a) (sl1 : sl_f (prd0 x)) ->
                  let sl1' : sl_list (prd1 x)
                           = sub_prd_sl_l #env sl0 csm0 (sl_list_of_f sl1) csm1 (prd_f x) in
                  SF.Tret a x (M.post_sl_t prd1) sl1')


(*** Soundness *)

let sound_SF_of_LV
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond u#a u#p env t csm prd)
      (sl0 : sl_list env)
      (sf : SF.prog_tree u#a u#0 u#p a (M.post_sl_t prd))
  : prop
  =
    (tree_req lc (Fl.flist_of_d sl0) <==> SF.tree_req sf) /\
    (forall (res : a) (sl1 : sl_f (prd res)) .
       tree_ens lc (Fl.flist_of_d sl0) res sl1 <==> SF.tree_ens sf res sl1)

val repr_SF_of_LV_sound
      (#env : vprop_list) (#a : Type) (#t : M.prog_tree a)
      (#csm : csm_t env) (#prd : prd_t a)
      (lc : lin_cond u#a u#p env t csm prd)
      (sl0 : sl_list env)
  : Lemma (sound_SF_of_LV lc sl0 (repr_SF_of_LV lc sl0))
