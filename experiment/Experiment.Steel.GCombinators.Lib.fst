module Experiment.Steel.GCombinators.Lib

module L = FStar.List.Pure
module M = Experiment.Steel.Repr.M

#set-options "--fuel 1 --ifuel 1"

(**** [make_combinator_steel] *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
inline_for_extraction
let make_combinator_steel__steel
      (#a : Type u#a) (s : G.erased (M.spec_r a)) (f : M.spc_steel_t SH.KSteel s)
      (#pre : G.erased M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : G.erased (M.post_t a)) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (G.reveal post x)))
  : M.repr_steel_t SH.KSteel a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.steel_f M.(fun () ->
      pre_eq.veq_g _;
      (**) elim_vpl_append s.spc_pre s.spc_ro;
      (**) let sl0'  = gget_f s.spc_pre in
      (**) let sl_ro = gget_f s.spc_ro in     
      (**) assert (s.M.spc_req sl0' sl_ro);
      let (x : a) = SH.steel_u f () in
      (**) let sl1'   = gget_f (s.spc_post x) in
      (**) let sl_ro' = gget_f s.spc_ro       in
      (**) assert (sl_ro' == sl_ro);
      (**) assert (s.M.spc_ens sl0' x sl1' sl_ro);
      (**) intro_vpl_append (s.spc_post x) s.spc_ro;
      (post_eq x).veq_g _;
      SA.return x
    )

inline_for_extraction
let make_combinator_steel__atomic
      (#a : Type u#a) (opened : Mem.inames) (s : G.erased (M.spec_r a)) (f : M.spc_steel_t (SH.KAtomic opened) s)
      (#pre : G.erased M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : G.erased (M.post_t a)) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (G.reveal post x)))
  : M.repr_steel_t (SH.KAtomic opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.atomic_f #opened M.(fun () ->
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
let make_combinator_steel__ghostI
      (#a : Type u#a) (opened : Mem.inames) (s : G.erased (M.spec_r a)) (f : M.spc_steel_t (SH.KGhostI opened) s)
      (#pre : G.erased M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : G.erased (M.post_t a)) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (G.reveal post x)))
  : M.repr_steel_t (SH.KGhostI opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.ghostI_f #opened M.(fun () ->
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

inline_for_extraction
let make_combinator_steel__ghost
      (#a : Type u#a) (opened : Mem.inames) (s : G.erased (M.spec_r a)) (f : M.spc_steel_t (SH.KGhost opened) s)
      (#pre : G.erased M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : G.erased (M.post_t a)) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (G.reveal post x)))
  : M.repr_steel_t (SH.KGhost opened) a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  =
    SH.ghost_f #opened M.(fun () ->
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
#pop-options

inline_for_extraction
let make_combinator_steel
      (ek : SH.effect_kind) (#a : Type u#a) (s : G.erased (M.spec_r a)) (f : M.spc_steel_t ek s)
      (#pre : G.erased M.pre_t) (pre_eq : Veq.vequiv pre (M.spc_pre1 s))
      (#post : G.erased (M.post_t a)) (post_eq : ((x : a) -> Veq.vequiv (M.spc_post1 s x) (G.reveal post x)))
  : M.repr_steel_t ek a pre post (M.gen_req s pre_eq post_eq) (M.gen_ens s pre_eq post_eq)
  = match ek with
  | SH.KSteel    -> make_combinator_steel__steel    s f pre_eq post_eq
  | SH.KAtomic o -> make_combinator_steel__atomic o s f pre_eq post_eq
  | SH.KGhostI o -> make_combinator_steel__ghostI o s f pre_eq post_eq
  | SH.KGhost  o -> make_combinator_steel__ghost  o s f pre_eq post_eq


(***** [lc_to_spc_steel_t] *)

type lc_repr_steel_t0
       (#a : Type) (ek : SH.effect_kind) (t : M.prog_tree a)
       (#env : vprop_list) (#csm : LV.csm_t env) (#prd : LV.prd_t a)
       (lc : LV.lin_cond u#a u#p env t csm prd {LV.lcsub_at_leaves lc})
  = M.repr_steel_t ek a env (LV2M.res_env_f env csm prd)
              (M.tree_req t (LV2M.repr_M_of_LV lc))
              (M.tree_ens t (LV2M.repr_M_of_LV lc))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
inline_for_extraction
let lc_to_spc_steel_t_steel__steel
      (#a : Type) (t : G.erased (M.prog_tree a))
      (#env : G.erased vprop_list) (#csm : G.erased (LV.csm_t env)) (#prd : G.erased (LV.prd_t a))
      (lc : G.erased (LV.lin_cond u#a u#p env t csm prd) {LV.lcsub_at_leaves lc})
      (f : lc_repr_steel_t0 SH.KSteel t lc)
  : M.spc_steel_t SH.KSteel (lc_spec_r lc)
  =
    let tc : G.erased (LV2M.lc_to_M lc) = LV2M.repr_M_of_LV lc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.steel_f (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.steel_u f () in
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
let lc_to_spc_steel_t_steel__atomic
      (opened : Mem.inames) (#a : Type) (t : G.erased (M.prog_tree a))
      (#env : G.erased vprop_list) (#csm : G.erased (LV.csm_t env)) (#prd : G.erased (LV.prd_t a))
      (lc : G.erased (LV.lin_cond u#a u#p env t csm prd) {LV.lcsub_at_leaves lc})
      (f : lc_repr_steel_t0 (SH.KAtomic opened) t lc)
  : M.spc_steel_t (SH.KAtomic opened) (lc_spec_r lc)
  =
    let tc : G.erased (LV2M.lc_to_M lc) = LV2M.repr_M_of_LV lc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.atomic_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.atomic_u f () in
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
let lc_to_spc_steel_t_steel__ghostI
      (opened : Mem.inames) (#a : Type) (t : G.erased (M.prog_tree a))
      (#env : G.erased vprop_list) (#csm : G.erased (LV.csm_t env)) (#prd : G.erased (LV.prd_t a))
      (lc : G.erased (LV.lin_cond u#a u#p env t csm prd) {LV.lcsub_at_leaves lc})
      (f : lc_repr_steel_t0 (SH.KGhostI opened) t lc)
  : M.spc_steel_t (SH.KGhostI opened) (lc_spec_r lc)
  =
    let tc : G.erased (LV2M.lc_to_M lc) = LV2M.repr_M_of_LV lc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.ghostI_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.ghostI_u f () in
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
let lc_to_spc_steel_t_steel__ghost
      (opened : Mem.inames) (#a : Type) (t : G.erased (M.prog_tree a))
      (#env : G.erased vprop_list) (#csm : G.erased (LV.csm_t env)) (#prd : G.erased (LV.prd_t a))
      (lc : G.erased (LV.lin_cond u#a u#p env t csm prd) {LV.lcsub_at_leaves lc})
      (f : lc_repr_steel_t0 (SH.KGhost opened) t lc)
  : M.spc_steel_t (SH.KGhost opened) (lc_spec_r lc)
  =
    let tc : G.erased (LV2M.lc_to_M lc) = LV2M.repr_M_of_LV lc in
    (**) LV2M.repr_M_of_LV_sound lc;
    SH.ghost_f #opened (fun () ->
      (**) let sl0    = gget_f (lc_pre lc)    in
      (**) let sl_ro0 = gget_f (lc_ro  lc)    in
      elim_vpl_filter_mask_append env csm;
      (**) let sl0'   = gget_f env            in
      let x = SH.ghost_u f () in
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
#pop-options

inline_for_extraction
let lc_to_spc_steel_t_steel
      (#ek : SH.effect_kind) (#a : Type) (t : G.erased (M.prog_tree a))
      (#env : G.erased vprop_list) (#csm : G.erased (LV.csm_t env)) (#prd : G.erased (LV.prd_t a))
      (lc : G.erased (LV.lin_cond u#a u#p env t csm prd) {LV.lcsub_at_leaves lc})
      (f : lc_repr_steel_t0 ek t lc)
  : M.spc_steel_t ek (lc_spec_r lc)
  = match ek with
    | SH.KSteel    -> lc_to_spc_steel_t_steel__steel    t lc f
    | SH.KAtomic o -> lc_to_spc_steel_t_steel__atomic o t lc f
    | SH.KGhost  o -> lc_to_spc_steel_t_steel__ghost  o t lc f
    | SH.KGhostI o -> lc_to_spc_steel_t_steel__ghostI o t lc f
