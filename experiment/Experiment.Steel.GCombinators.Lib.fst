module Experiment.Steel.GCombinators.Lib

include Experiment.Steel.Tac
include Experiment.Steel.Tac.LV

module U      = Learn.Util
module L      = FStar.List.Pure
module M      = Experiment.Steel.Repr.M
module Ll     = Learn.List
module Fl     = Learn.FList
module SH     = Experiment.Steel.Steel
module LV     = Experiment.Steel.Repr.LV
module SF     = Experiment.Steel.Repr.SF
module SA     = Steel.Effect.Atomic
module Veq    = Experiment.Steel.VEquiv
module Fun    = Experiment.Repr.Fun
module Mem    = Steel.Memory
module Msk    = Learn.List.Mask
module Perm   = Learn.Permutation
module LV2M   = Experiment.Steel.Repr.LV_to_M
module LV2SF  = Experiment.Steel.Repr.LV_to_SF
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun

open Steel.Effect
open Steel.Effect.Atomic
open Experiment.Steel.VPropList
open Experiment.Steel.Interface
open FStar.Tactics

#set-options "--fuel 1 --ifuel 1"


let __delta_perm : list string = [
    `%Perm.perm_f_to_list; `%Perm.comp; `%Perm.perm_f_append; `%Perm.mk_perm_f; `%Perm.perm_f_of_pair;
    `%Perm.pequiv_append_swap; `%Perm.pequiv_refl; `%Perm.id_n;
    `%LV.eij_equiv; `%LV.eij_equiv_f
  ]

(*** [make_combinator] *)

/// [make_combinator] is used to build a new combinator. It handle the [pre_eq] and [post_eq] of [M.TCgen].

#push-options "--fuel 0 --ifuel 0"
inline_for_extraction
let make_combinator_steel
      (#a : Type u#a) (s : M.spec_r a) (f : M.spc_steel_t SH.KSteel s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t SH.KSteel a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.steel_f (fun () ->
      pre_eq.veq_g _;
      (**) elim_vpl_append s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.spc_req sl0' sl_ro);
      let (x : a) = SH.steel_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.spc_ens sl0' x sl1' sl_ro);
      (**) intro_vpl_append (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      SA.return x
    )

inline_for_extraction
let make_combinator_steel_atomic
      (#a : Type u#a) (opened : Mem.inames) (s : M.spec_r a) (f : M.spc_steel_t (SH.KAtomic opened) s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t (SH.KAtomic opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.atomic_f #opened (fun () ->
      pre_eq.veq_g _;
      (**) elim_vpl_append s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.spc_req sl0' sl_ro);
      let (x : a) = SH.atomic_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.spc_ens sl0' x sl1' sl_ro);
      (**) intro_vpl_append (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      SA.return x
    )

inline_for_extraction
let make_combinator_steel_ghost
      (#a : Type u#a) (opened : Mem.inames) (s : M.spec_r a) (f : M.spc_steel_t (SH.KGhost opened) s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t (SH.KGhost opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.ghost_f #opened (fun () ->
      pre_eq.veq_g _;
      (**) elim_vpl_append s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.spc_req sl0' sl_ro);
      let (x : a) = SH.ghost_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.spc_ens sl0' x sl1' sl_ro);
      (**) intro_vpl_append (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      x
    )

inline_for_extraction
let make_combinator_steel_ghostI
      (#a : Type u#a) (opened : Mem.inames) (s : M.spec_r a) (f : M.spc_steel_t (SH.KGhostI opened) s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t (SH.KGhostI opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.ghostI_f #opened (fun () ->
      pre_eq.veq_g _;
      (**) elim_vpl_append s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.spc_req sl0' sl_ro);
      let (x : a) = SH.ghostI_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.spc_ens sl0' x sl1' sl_ro);
      (**) intro_vpl_append (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      SA.return x
    )
#pop-options

inline_for_extraction
let make_combinator_steel_ek
      (ek : SH.effect_kind) (#a : Type u#a) (s : M.spec_r a) (f : M.spc_steel_t ek s)
      (#pre : M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : M.post_t a) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (post x)))
  : M.repr_steel_t ek a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  = match ek with
  | SH.KSteel         -> make_combinator_steel               s f pre_eq post_eq
  | SH.KAtomic opened -> make_combinator_steel_atomic opened s f pre_eq post_eq
  | SH.KGhost  opened -> make_combinator_steel_ghost  opened s f pre_eq post_eq
  | SH.KGhostI opened -> make_combinator_steel_ghostI opened s f pre_eq post_eq

[@@ __repr_M__]
inline_for_extraction
let make_combinator
      (a : Type) (ek : SH.effect_kind) (gen_tac : M.gen_tac_t) (gen_c : M.spec_r a -> Type u#(max a p 2))
      (f : (s : M.spec_r a) -> (sh : gen_c s) -> M.spc_steel_t ek s)
  : M.repr u#a u#p ek a
  = {
    repr_tree  = M.Tgen a gen_tac gen_c;
    repr_steel = (fun pre post c ->
                    let M.TCgen s sh _ pre_eq _ post_eq = c in
                    make_combinator_steel_ek ek s (f s sh) pre_eq post_eq)
  }


(*** [gen_sf_Tspec] *)

/// A [LV.gen_sf] can always be built using a [SF.Tspec] with the expected specifications.

#push-options "--fuel 1"
[@@ __LV2SF__]
let gen_sf_Tspec (#a : Type) (s : M.spec_r a)
  : LV.gen_sf s
  = fun (sl0 : sl_f s.spc_pre) (sl_ro : sl_f s.spc_ro) ->
    SF.Tspec a (M.post_sl_t s.spc_post)
             (requires s.spc_req sl0 sl_ro)
             (ensures  fun x sl1 -> s.spc_ens sl0 x sl1 sl_ro)
#pop-options


(*** [lc_spec_r] *)

/// [lc_spec_r lc] is the specification (given as a [M.spec_r]) resulting from the [LV.lin_cond] [lc].
/// [lc_sf] provides a corresponding [gen_sf] (that is a [SF.prog_tree] with an equivalent specification).
/// [lc_wp] provides a sound (but theoretically not complete) weakest-precondition.
/// [lc_to_spc_steel_t] gives a Steel implementation.

[@@ __cond_solver__; __LV2SF__]
let lc_pre
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
  : M.pre_t
  = Msk.(filter_mask csm env)

[@@ __cond_solver__; __LV2SF__]
let lc_post
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
  : M.post_t a
  = prd

[@@ __cond_solver__; __LV2SF__]
let lc_ro
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
  : vprop_list
  = Msk.(filter_mask (mask_not csm) env)

let lc_req
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (sl_ro : sl_f (lc_ro lc))
  : Type0
  = LV.tree_req lc (append_vars_mask csm sl0 sl_ro)

let lc_ens
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (x : a) (sl1 : sl_f (lc_post lc x)) (sl_ro : sl_f (lc_ro lc))
  : Type0
  = LV.tree_ens lc (append_vars_mask csm sl0 sl_ro) x sl1

let lc_spec_r
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
  : M.spec_r a
  = M.Mkspec_r (lc_pre lc) (lc_post lc) (lc_ro lc) (lc_req lc) (lc_ens lc)


(***** [lc_sf] *)

[@@ __LV2SF__]
let lc_sf
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
  : LV.gen_sf (lc_spec_r lc)
  =
    fun (sl0 : sl_f (lc_pre lc)) (sl_ro : sl_f (lc_ro lc)) ->
      let sl0' = LV2SF.append_vars_mask_l csm (Fl.dlist_of_f sl0) (Fl.dlist_of_f sl_ro) in
      (**) LV2SF.repr_SF_of_LV_sound lc sl0';
      LV2SF.repr_SF_of_LV lc sl0'

let rew_lc_sf_req
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (sl_ro : sl_f (lc_ro lc))
  : squash (lc_req lc sl0 sl_ro <==> SF.tree_req (lc_sf lc sl0 sl_ro))
  = ()

let rew_lc_sf_ens
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (x : a) (sl1 : sl_f (lc_post lc x)) (sl_ro : sl_f (lc_ro lc))
  : squash (lc_ens lc sl0 x sl1 sl_ro <==> SF.tree_ens (lc_sf lc sl0 sl_ro) x sl1)
  = ()


(***** [lc_wp] *)

// We mark [lc_wp] as GTot to avoid a "Substitution must be fully applied" error from F* when
// extracting the .krml of a module that depends on this one.
[@@ __LV2SF__]
let lc_wp
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (sl_ro : sl_f (lc_ro lc))
  : GTot (pure_wp SF2Fun.(sl_tys_v ({val_t = a; sel_t = M.post_sl_t prd})))
  =
    let sf : SF.prog_tree a (M.post_sl_t prd)
           = lc_sf lc sl0 sl_ro       in
    let fn : Fun.prog_tree SF2Fun.({val_t = a; sel_t = M.post_sl_t prd})
           = SF2Fun.repr_Fun_of_SF sf in
    Fun.tree_wp fn

let lc_wp_sound
      (#a : Type) (#env : vprop_list) (#t : M.prog_tree a) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env t csm prd)
      (sl0 : sl_f (lc_pre lc)) (sl_ro : sl_f (lc_ro lc))
      (post : pure_post SF2Fun.(sl_tys_v ({val_t = a; sel_t = M.post_sl_t prd})))
  : Lemma (requires lc_wp lc sl0 sl_ro post)
          (ensures  lc_req lc sl0 sl_ro /\
                   (forall (x : a) (sl1 : sl_f (prd x)) .
                    lc_ens lc sl0 x sl1 sl_ro ==> post SF2Fun.({val_v = x; sel_v = sl1})))
  =
    let sl0' = LV2SF.append_vars_mask_l csm (Fl.dlist_of_f sl0) (Fl.dlist_of_f sl_ro) in
    let sf = LV2SF.repr_SF_of_LV lc sl0' in
    LV2SF.repr_SF_of_LV_sound lc sl0';
    let fn = SF2Fun.repr_Fun_of_SF sf    in
    SF2Fun.repr_Fun_of_SF_req sf;
    Fun.tree_wp_sound fn post;
    assert (lc_req lc sl0 sl_ro);
    introduce forall (x : a) (sl1 : sl_f (prd x)) .
              lc_ens lc sl0 x sl1 sl_ro ==> post SF2Fun.({val_v = x; sel_v = sl1})
      with SF2Fun.repr_Fun_of_SF_ens sf x sl1


(***** [lc_to_spc_steel_t] *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
inline_for_extraction
let lc_to_spc_steel_t__steel
      (#a : Type) (mr : M.repr SH.KSteel a)
      (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env mr.repr_tree csm prd {LV.lcsub_at_leaves lc})
  : M.spc_steel_t SH.KSteel (lc_spec_r lc)
  =
    let tc = LV2M.repr_M_of_LV lc                              in
    let sf = mr.repr_steel env (LV2M.res_env_f env csm prd) tc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.steel_f (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.steel_u sf () in
      (**) let sl1'   = gget_f L.(lc_post lc x @ lc_ro lc) in
      elim_vpl_append (lc_post lc x) (lc_ro lc);
      (**) let sl1    = gget_f (lc_post lc x) in
      (**) let sl_ro1 = gget_f (lc_ro   lc)   in
      (**) assert (Ghost.reveal sl1' == LV2M.res_env_app sl1 sl_ro1);
      (**) assert (M.tree_ens _ tc sl0' x sl1');
      (**) filter_append_vars_mask csm sl0 sl_ro0;
      (**) assert (LV.tree_ens lc sl0' x sl1 /\ sl_ro0 == sl_ro1);
      SA.return x
    )

inline_for_extraction
let lc_to_spc_steel_t__atomic
      (opened : Mem.inames) (#a : Type) (mr : M.repr (SH.KAtomic opened) a)
      (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env mr.repr_tree csm prd {LV.lcsub_at_leaves lc})
  : M.spc_steel_t (SH.KAtomic opened) (lc_spec_r lc)
  =
    let tc = LV2M.repr_M_of_LV lc                              in
    let sf = mr.repr_steel env (LV2M.res_env_f env csm prd) tc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.atomic_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.atomic_u sf () in
      (**) let sl1'   = gget_f L.(lc_post lc x @ lc_ro lc) in
      elim_vpl_append (lc_post lc x) (lc_ro lc);
      (**) let sl1    = gget_f (lc_post lc x) in
      (**) let sl_ro1 = gget_f (lc_ro   lc)   in
      (**) assert (Ghost.reveal sl1' == LV2M.res_env_app sl1 sl_ro1);
      (**) assert (M.tree_ens _ tc sl0' x sl1');
      (**) filter_append_vars_mask csm sl0 sl_ro0;
      (**) assert (LV.tree_ens lc sl0' x sl1 /\ sl_ro0 == sl_ro1);
      SA.return x
    )

inline_for_extraction
let lc_to_spc_steel_t__ghost
      (opened : Mem.inames) (#a : Type) (mr : M.repr (SH.KGhost opened) a)
      (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env mr.repr_tree csm prd {LV.lcsub_at_leaves lc})
  : M.spc_steel_t (SH.KGhost opened) (lc_spec_r lc)
  =
    let tc = LV2M.repr_M_of_LV lc                              in
    let sf = mr.repr_steel env (LV2M.res_env_f env csm prd) tc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.ghost_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.ghost_u sf () in
      (**) let sl1'   = gget_f L.(lc_post lc x @ lc_ro lc) in
      elim_vpl_append (lc_post lc x) (lc_ro lc);
      (**) let sl1    = gget_f (lc_post lc x) in
      (**) let sl_ro1 = gget_f (lc_ro   lc)   in
      (**) assert (Ghost.reveal sl1' == LV2M.res_env_app sl1 sl_ro1);
      (**) assert (M.tree_ens _ tc sl0' x sl1');
      (**) filter_append_vars_mask csm sl0 sl_ro0;
      (**) assert (LV.tree_ens lc sl0' x sl1 /\ sl_ro0 == sl_ro1);
      (**) noop ();
      x
    )

inline_for_extraction
let lc_to_spc_steel_t__ghostI
      (opened : Mem.inames) (#a : Type) (mr : M.repr (SH.KGhostI opened) a)
      (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env mr.repr_tree csm prd {LV.lcsub_at_leaves lc})
  : M.spc_steel_t (SH.KGhostI opened) (lc_spec_r lc)
  =
    let tc = LV2M.repr_M_of_LV lc                              in
    let sf = mr.repr_steel env (LV2M.res_env_f env csm prd) tc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.ghostI_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.ghostI_u sf () in
      (**) let sl1'   = gget_f L.(lc_post lc x @ lc_ro lc) in
      elim_vpl_append (lc_post lc x) (lc_ro lc);
      (**) let sl1    = gget_f (lc_post lc x) in
      (**) let sl_ro1 = gget_f (lc_ro   lc)   in
      (**) assert (Ghost.reveal sl1' == LV2M.res_env_app sl1 sl_ro1);
      (**) assert (M.tree_ens _ tc sl0' x sl1');
      (**) filter_append_vars_mask csm sl0 sl_ro0;
      (**) assert (LV.tree_ens lc sl0' x sl1 /\ sl_ro0 == sl_ro1);
      SA.return x
    )
#pop-options

inline_for_extraction
let lc_to_spc_steel_t
      (#ek : SH.effect_kind) (#a : Type) (mr : M.repr ek a)
      (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
      (lc : LV.lin_cond u#a u#p env mr.repr_tree csm prd {LV.lcsub_at_leaves lc})
  : M.spc_steel_t ek (lc_spec_r lc)
  =
    match ek with
    | SH.KSteel    -> lc_to_spc_steel_t__steel    mr lc
    | SH.KAtomic o -> lc_to_spc_steel_t__atomic o mr lc
    | SH.KGhost  o -> lc_to_spc_steel_t__ghost  o mr lc
    | SH.KGhostI o -> lc_to_spc_steel_t__ghostI o mr lc


(*** Building [lin_cond] *)

(**** Enforcing [lcsub_at_leaves] *)

[@@ __cond_solver__]
let build_lcsub_at_leaves_lc
       (env : vprop_list) (#a : Type) (t : M.prog_tree a)
       (csm : LV.csm_t env) (prd : LV.prd_t a)
       (lc0 : LV.lin_cond u#a u#p env #a t csm prd)
  : lc : LV.lin_cond env #a t csm prd { LV.lcsub_at_leaves lc }
  =
    (**) LV.lc_sub_push_at_leaves env lc0;
    LV.lc_sub_push lc0


(**** With exact specifications *)

[@@ __cond_solver__]
let __build_lin_cond_exact
      (env : vprop_list) (#a : Type) (t : M.prog_tree a)
      (csm0 csm1 : LV.csm_t env) (prd0 prd1 : LV.prd_t a)
      (lc : LV.lin_cond env t csm0 prd0)
      (csm_le : b2t (Msk.mask_le_eff csm0 csm1))
      (prd_f : (x : a) -> Perm.pequiv_list L.(prd0 x @ filter_diff csm0 csm1 env) (prd1 x))
  : LV.lin_cond env t csm1 prd1
  =
    Ll.list_extensionality (Msk.mask_or csm0 csm1) csm1 (fun i -> ());
    lcsub_add_csm env t csm0 prd0 lc csm1 prd1 prd_f

/// Solves a goal [lin_cond env t prd csm] where [prd] and [csm] are concrete terms.
let build_lin_cond_exact (fr : flags_record) (ctx : cs_context) : Tac unit
  =
    apply (`__build_lin_cond_exact);
    // lc
    build_lin_cond fr None;
    // csm_le
    norm_lc ();
    cs_try (fun () ->
        norm [delta_only [`%Msk.mask_le_eff]; iota; zeta; primops];
        trefl ()
      ) fr ctx (fun m -> fail (m Fail_csm_le []));
    // prd_f
    let x = intro () in
    norm_lc ();
    build_pequiv_list fr ctx

#push-options "--fuel 5"
let test_lin_cond_exact (v : int -> vprop')
  : LV.lin_cond [v 0; v 1; v 2]
      M.(Tspec unit (M.spec_r_exact (Mkspec_r [v 0] (fun _ -> [v 3]) [v 1] (fun _ _ -> True) (fun _ _ _ _ -> True))))
      [true; false; true] (fun _ -> [v 2; v 3])
  = _ by (build_lin_cond_exact default_flags dummy_ctx)
#pop-options


(**** [lin_cond_st] *)

/// [lin_cond_st env t must_csm must_prd csm1 prd1] ("lin_cond such that") is used to build a [lin_cond] consuming at
/// least [must_csm] and producing at least [must_prd]. It allows other variables to be consumed ([csm1]) or
/// produced ([prd1]).

#push-options "--ifuel 0 --fuel 0"

type lin_cond_st
       (env : vprop_list) (#a : Type) (t : M.prog_tree a)
       (must_csm : LV.csm_t env) (must_prd : LV.prd_t a)
       (csm1 : LV.csm_t Msk.(filter_mask (mask_not must_csm) env)) (prd1 : LV.prd_t a)
  = lc : LV.lin_cond u#a u#p env #a t (Msk.mask_comp_or must_csm csm1) L.(fun x -> must_prd x @ prd1 x)
       { LV.lcsub_at_leaves lc }

let pequiv_append_02 (#a : Type) (l0 l1 l2 l3 : list a)
  : Perm.pequiv L.(l0 @ l1 @ l2 @ l3) L.(l0 @ l2 @ l1 @ l3)
  =
    L.append_assoc l1 l2 l3; L.append_assoc l2 l1 l3;
    U.cast _
    Perm.(pequiv_append (pequiv_refl l0)
         (pequiv_append (pequiv_append_swap l1 l2)
                        (pequiv_refl l3)))

[@@ __cond_solver__]
let build_lin_cond_st_prd_f
      (prd0 env must_prd : vprop_list) (must_csm : LV.csm_t env)
      (post_f : LV.eq_injection_l must_prd L.(prd0 @ env))
  : (let n0 = L.length prd0          in
     let n1 = L.length env           in
     let m0 = LV.eij_trg_mask post_f in
     (**) L.splitAt_length n0 m0;
     let m0a, m0b = L.splitAt n0 m0  in
     let m0a : Ll.vec n0 bool = m0a  in
     let m0b : Ll.vec n1 bool = m0b  in
     Perm.pequiv_list
      L.(prd0 @ Msk.(filter_mask (mask_or m0b must_csm) env))
      L.(must_prd @ Msk.(filter_mask (mask_not m0a) prd0) @ filter_diff m0b must_csm env))
  = Msk.(
    let n0 = L.length prd0          in
    let n1 = L.length env           in
    let m0 = LV.eij_trg_mask post_f in
    (**) L.splitAt_length n0 m0;
    let m0a, m0b = L.splitAt n0 m0  in
    let m0a : Ll.vec n0 bool = m0a  in
    let m0b : Ll.vec n1 bool = m0b  in

    let must_csm' = mask_diff m0b must_csm in

    let flt00 = filter_mask m0a prd0                                   in
    let flt01 = filter_mask (mask_not m0a) prd0                        in
    let flt10 = filter_mask m0b env                                    in
    let flt11 = filter_mask must_csm' (filter_mask (mask_not m0b) env) in

    Ll.list_extensionality (mask_or m0b must_csm) (mask_comp_or m0b must_csm') (fun i -> ());
    assert (filter_diff m0b must_csm env == flt11);
    U.assert_by L.(filter_mask m0 (prd0 @ env) == flt00 @ flt10) (fun () ->
      Ll.lemma_splitAt_append n0 m0;
      filter_mask_append m0a m0b prd0 env);

    let f0 : Perm.pequiv L.(flt00 @ flt10) must_prd
      = U.cast _ (LV.eij_equiv post_f)           in
    let f1 : Perm.pequiv prd0 L.(flt00 @ flt01)
      = mask_pequiv_append m0a prd0              in
    let f2 : Perm.pequiv (filter_mask (mask_comp_or m0b must_csm') env) L.(flt10 @ flt11)
      = mask_or_pequiv_append m0b must_csm' env  in

    L.append_assoc flt00 flt01 L.(flt10 @ flt11);
    let f3 : Perm.pequiv L.(prd0 @ filter_mask (mask_comp_or m0b must_csm') env)
                         L.(flt00 @ flt01 @ flt10 @ flt11)
      = Perm.pequiv_append f1 f2                 in
    L.append_assoc flt00 flt10 L.(flt01 @ flt11);
    let f4 : Perm.pequiv L.(flt00 @ flt01 @ flt10 @ flt11)
                         L.((flt00 @ flt10) @ (flt01 @ flt11))
      = pequiv_append_02 flt00 flt01 flt10 flt11 in

    let f : Perm.pequiv L.(prd0 @ filter_mask (mask_comp_or m0b must_csm') env)
                        L.(must_prd @ (flt01 @ flt11))
      = Perm.(pequiv_trans f3
             (pequiv_trans f4
             (pequiv_append f0 (pequiv_refl L.(flt01 @ flt11)))))
    in Perm.perm_f_to_list f)

[@@ __cond_solver__]
let __build_lin_cond_st
      (env : vprop_list) (#a : Type) (t : M.prog_tree a)
      (csm0 : LV.csm_t env) (prd0 : LV.prd_t a)
      (ct : LV.lin_cond env t csm0 prd0)
      (must_csm : LV.csm_t env) (must_prd : LV.prd_t a)
      (post_f : (x : a) -> LV.eq_injection_l (must_prd x) (LV.res_env env csm0 (prd0 x)))
      (csm' : Msk.(mask_t (filter_mask (mask_not csm0) env)))
      (csm'_eq : (x : a) -> squash (
        let n0 = L.length (prd0 x)          in
        let m0 = LV.eij_trg_mask (post_f x) in
        (**) L.splitAt_length n0 m0;
        csm' = (L.splitAt n0 m0)._2))
  : lin_cond_st u#a u#p env t must_csm must_prd
        Msk.(mask_diff must_csm (mask_comp_or csm0 csm'))
        (fun x ->
          let n0 = L.length (prd0 x)          in
          let m0 = LV.eij_trg_mask (post_f x) in
          (**) L.splitAt_length n0 m0;
          let m0a : Ll.vec n0 bool = (L.splitAt n0 m0)._1 in
          L.(Msk.filter_mask (Msk.mask_not m0a) (prd0 x)
           @ filter_diff (Msk.mask_comp_or csm0 csm') must_csm env))
  =
    let csm1 : Msk.(mask_t (filter_mask (mask_not csm0) env))
             = Msk.(mask_or csm' (mask_diff csm0 must_csm))     in
    let prd1 x =
      let n0 = L.length (prd0 x)                                in
      let m0 = LV.eij_trg_mask (post_f x)                       in
      (**) L.splitAt_length n0 m0;
      let m0a : Ll.vec n0 bool = (L.splitAt n0 m0)._1           in
      L.(Msk.filter_mask (Msk.mask_not m0a) (prd0 x)
       @ filter_diff (Msk.mask_comp_or csm0 csm') must_csm env) in
    Msk.(calc (==) {
      LV.bind_csm env csm0 csm1 <: list bool;
    == { Ll.list_extensionality_sq (fun i -> ()) }
      mask_or must_csm (mask_comp_or csm0 csm');
    == { mask_comp_or_mask_diff must_csm (mask_comp_or csm0 csm') }
      mask_comp_or must_csm (mask_diff must_csm (mask_comp_or csm0 csm'));
    });
    let prd_f (x : a) : Perm.pequiv_list (LV.sub_prd env csm0 (prd0 x) csm1) L.(must_prd x @ prd1 x)
      =
        let n0 = L.length (prd0 x)              in
        let n1 = Msk.(mask_len (mask_not csm0)) in
        let m0 = LV.eij_trg_mask (post_f x)     in
        (**) L.splitAt_length n0 m0;
        let m0a, m0b = L.splitAt n0 m0          in
        let m0a : Ll.vec n0 bool = m0a          in
        let m0b : Ll.vec n1 bool = m0b          in
        U.assert_by (csm' == m0b) (fun () -> csm'_eq x);
        let env1      = Msk.(filter_mask (mask_not csm0) env) in
        let must_csm1 = Msk.(mask_diff csm0 must_csm)         in
        assert (LV.sub_prd env csm0 (prd0 x) csm1
          == L.(prd0 x @ Msk.(filter_mask (mask_or m0b must_csm1) env1)));
        Msk.(calc (==) {
          filter_diff m0b (mask_diff csm0 must_csm) (filter_mask (mask_not csm0) env);
        == { }
          filter_mask (mask_diff m0b (mask_diff csm0 must_csm))
            (filter_mask (mask_not m0b) (filter_mask (mask_not csm0) env));
        == { filter_mask_and (mask_not csm0) (mask_not m0b) must_csm;
             filter_mask_and (mask_not csm0) (mask_not m0b) env }
          filter_mask (filter_mask (mask_comp_and (mask_not csm0) (mask_not m0b)) must_csm)
            (filter_mask (mask_comp_and (mask_not csm0) (mask_not m0b)) env);
        == { mask_not_comp_or csm0 m0b }
          filter_mask (filter_mask (mask_not (mask_comp_or csm0 m0b)) must_csm)
            (filter_mask (mask_not (mask_comp_or csm0 m0b)) env);
        == { }
          filter_diff (mask_comp_or csm0 m0b) must_csm env;
        });
        assert L.(must_prd x @ prd1 x
               == must_prd x @ Msk.(filter_mask (mask_not m0a) (prd0 x)) @ filter_diff m0b must_csm1 env1);
        build_lin_cond_st_prd_f (prd0 x) env1 (must_prd x) must_csm1 (post_f x)
    in
    let ct' = LV.LCsub env csm0 prd0 ct csm1 L.(fun x -> must_prd x @ prd1 x) prd_f in
    (**) LV.lc_sub_push_at_leaves env ct';
    LV.lc_sub_push ct'


noeq
type test_lin_cond_st env #a t must_csm must_prd =
  | TestLinCondSt : (csm1 : _) -> (prd1 : _) ->
                    lin_cond_st env #a t must_csm must_prd csm1 prd1 ->
                    test_lin_cond_st env t must_csm must_prd

#push-options "--fuel 5"
let test_lin_cond_st_0 (v : int -> vprop')
  : test_lin_cond_st [v 0; v 1; v 2; v 3]
      M.(Tspec unit (M.spec_r_exact (Mkspec_r [v 0] (fun _ -> [v 4; v 5]) [v 1] (fun _ _ -> True) (fun _ _ _ _ -> True))))
      [true; false; true; false] (fun _ -> [v 4; v 1])
  = _ by (
    apply (`TestLinCondSt);
    apply_raw (`__build_lin_cond_st);
    // ct
    dismiss (); dismiss ();
    build_lin_cond default_flags None;
    // post_f
    let x = intro () in
    norm_lc ();
    build_eq_injection_l default_flags dummy_ctx;
    // csm'_eq
    dismiss ();
    let x = intro () in
    norm_lc ();
    trefl ()
  )
#pop-options

[@@ __cond_solver__]
let __normalize_lin_cond_st
       (env : vprop_list) (#a : Type) (t : M.prog_tree a)
       (must_csm : LV.csm_t env) (must_prd : LV.prd_t a)
       (csm1 : LV.csm_t Msk.(filter_mask (mask_not must_csm) env)) (prd1 : LV.prd_t a)
       (lc : lin_cond_st env t must_csm must_prd csm1 prd1)
       (lc1 : lin_cond_st env t must_csm must_prd csm1 prd1)
       (_ : squash (lc1 == lc))
       (csm2 : LV.csm_t Msk.(filter_mask (mask_not must_csm) env)) (prd2 : LV.prd_t a)
       (_ : squash (csm2 == csm1 /\ prd2 == prd1))
  : lin_cond_st u#a u#p env t must_csm must_prd csm2 prd2
  = lc1

#pop-options

#push-options "--ifuel 1"
/// Solves a goal [lin_cond_st env t must_csm must_prd ?csm1 ?prd1]
let build_lin_cond_st (fr : flags_record) (ctx : cs_context) : Tac unit
  =
    apply_raw (`__normalize_lin_cond_st);
    // lc
      dismiss (); dismiss ();
      apply_raw (`__build_lin_cond_st);
      // ct
      dismiss (); dismiss ();
      build_lin_cond fr None;
      // post_f
      let x = intro () in
      norm_lc ();
      build_eq_injection_l fr ctx;
      // csm'_eq
      dismiss ();
      let x = intro () in
      norm_lc ();
      cs_try trefl fr ctx (fun m -> fail (m (Fail_dependency "csm" x) []));
    // lc1 <-
    dismiss ();
    norm [
      delta_only (L.append __delta_list (L.append __delta_perm [
        `%L.splitAt; `%L.mem; `%Mktuple2?._1; `%Mktuple2?._2; `%L.map2;
        `%pequiv_append_02]));
      delta_attr [`%__cond_solver__; `%Learn.Tactics.Util.__tac_helper__; `%Msk.__mask__; `%LV.__lin_cond__];
      delta_qualifier ["unfold"];
      iota; zeta; primops];
    trefl ();
    // csm2, prd2 <-
    norm_lc ();
    split (); trefl (); trefl ()
#pop-options
