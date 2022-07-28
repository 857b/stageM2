module Experiment.Steel.Repr.M

module T = FStar.Tactics
module L = FStar.List.Pure

#set-options "--ide_id_info_off"

(*** [repr_steel_t] *)

// TODO? avoid the duplication due to the several Steel effects by using meta-programming

inline_for_extraction noextract
let repr_steel_subcomp__steel
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (G.reveal post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t SH.KSteel a pre post req_f ens_f)
  : repr_steel_t SH.KSteel a pre post req_g ens_g
  = SH.steel_f (fun () ->
      (**) let sl0 = gget_f pre in
      (**) pf_req sl0;
      let x = SH.steel_u r () in
      (**) let sl1 = gget_f (G.reveal post x) in
      (**) pf_ens sl0 x sl1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_steel_subcomp__atomic
      (#a : Type) (opened : Mem.inames) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (G.reveal post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t (SH.KAtomic opened) a pre post req_f ens_f)
  : repr_steel_t (SH.KAtomic opened) a pre post req_g ens_g
  = SH.atomic_f (fun () ->
      (**) let sl0 = gget_f pre in
      (**) pf_req sl0;
      let x = SH.atomic_u r () in
      (**) let sl1 = gget_f (G.reveal post x) in
      (**) pf_ens sl0 x sl1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_steel_subcomp__ghostI
      (#a : Type) (opened : Mem.inames) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (G.reveal post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t (SH.KGhostI opened) a pre post req_f ens_f)
  : repr_steel_t (SH.KGhostI opened) a pre post req_g ens_g
  = SH.ghostI_f (fun () ->
      (**) let sl0 = gget_f pre in
      (**) pf_req sl0;
      let x = SH.ghostI_u r () in
      (**) let sl1 = gget_f (G.reveal post x) in
      (**) pf_ens sl0 x sl1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let repr_steel_subcomp__ghost
      (#a : Type) (opened : Mem.inames) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (G.reveal post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t (SH.KGhost opened) a pre post req_f ens_f)
  : repr_steel_t (SH.KGhost opened) a pre post req_g ens_g
  = SH.ghost_f (fun () ->
      (**) let sl0 = gget_f pre in
      (**) pf_req sl0;
      let x = SH.ghost_u r () in
      (**) let sl1 = gget_f (G.reveal post x) in
      (**) pf_ens sl0 x sl1;
      noop ();
      x)

inline_for_extraction noextract
let repr_steel_subcomp
      (ek : SH.effect_kind) (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a))
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (sl0 : sl_f pre) ->
                Lemma (requires req_g sl0) (ensures req_f sl0))
      (pf_ens : (sl0 : sl_f pre) -> (x : a) -> (sl1 : sl_f (G.reveal post x)) ->
                Lemma (requires req_f sl0 /\ req_g sl0 /\ ens_f sl0 x sl1) (ensures ens_g sl0 x sl1))
      (r : repr_steel_t ek a pre post req_f ens_f)
  : repr_steel_t ek a pre post req_g ens_g
  = match ek with
  | SH.KSteel    -> repr_steel_subcomp__steel    req_f ens_f req_g ens_g pf_req pf_ens r
  | SH.KAtomic o -> repr_steel_subcomp__atomic o req_f ens_f req_g ens_g pf_req pf_ens r
  | SH.KGhostI o -> repr_steel_subcomp__ghostI o req_f ens_f req_g ens_g pf_req pf_ens r
  | SH.KGhost  o -> repr_steel_subcomp__ghost  o req_f ens_f req_g ens_g pf_req pf_ens r


inline_for_extraction noextract
let steel_of_repr
      (#ek : SH.effect_kind)
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : G.erased (to_repr_t a pre post req ens))
      (f : repr_steel_t ek a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.steel a pre post req ens ek
  =
    (**) tr.r_pre_eq ();
    (**) FStar.Classical.forall_intro tr.r_post_eq;
    (**) FStar.Classical.forall_intro_2 reveal_equiv;
    SH.steel_subcomp_no_frame
      _ _ req ens
      (tr.r_pre_eq ()) (fun x -> tr.r_post_eq x)
      (SH.intro_subcomp_no_frame_pre _ _ _ _ _ _
        (fun h0      -> tr.r_req_eq h0)
        (fun h0 x h1 -> tr.r_ens_eq h0 x h1))
      f

inline_for_extraction noextract
let repr_of_steel
      (#ek : SH.effect_kind)
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : G.erased (to_repr_t a pre post req ens))
      ($f  : SH.steel a pre post req ens ek)
  : repr_steel_t ek a tr.r_pre tr.r_post tr.r_req tr.r_ens
  =
    (**) tr.r_pre_eq ();
    (**) FStar.Classical.forall_intro tr.r_post_eq;
    (**) FStar.Classical.forall_intro_2 reveal_equiv;
    SH.steel_subcomp_no_frame
      req ens _ _
      () (fun _ -> ())
      (SH.intro_subcomp_no_frame_pre _ _ _ _ _ _
        (fun (h0 : hmem (vprop_of_list tr.r_pre)) ->
           tr.r_req_eq h0)
        (fun (h0 : hmem (vprop_of_list tr.r_pre)) x (h1 : hmem (vprop_of_list (tr.r_post x))) ->
           tr.r_ens_eq h0 x h1))
      f


#push-options "--ifuel 0 --fuel 0"
inline_for_extraction noextract
let spec_r_of_find_ro__steel
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a)) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : G.erased (spec_find_ro a pre post req ens))
      (f : repr_steel_t SH.KSteel a pre post req ens)
  : spc_steel_t SH.KSteel sro.sro_spc
  = SH.steel_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) intro_vpl_append sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) change_vpl_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.steel_u f ()     in
      (**) let sl1'   = gget_f (G.reveal post x) in
      (**) change_vpl_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) elim_vpl_append (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let spec_r_of_find_ro__atomic
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a)) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : G.erased (spec_find_ro a pre post req ens))
      (#opened : Mem.inames) (f : repr_steel_t (SH.KAtomic opened) a pre post req ens)
  : spc_steel_t (SH.KAtomic opened) sro.sro_spc
  = SH.atomic_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) intro_vpl_append sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) change_vpl_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.atomic_u f ()    in
      (**) let sl1'   = gget_f (G.reveal post x) in
      (**) change_vpl_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) elim_vpl_append (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let spec_r_of_find_ro__ghostI
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a)) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : G.erased (spec_find_ro a pre post req ens))
      (#opened : Mem.inames) (f : repr_steel_t (SH.KGhostI opened) a pre post req ens)
  : spc_steel_t (SH.KGhostI opened) sro.sro_spc
  = SH.ghostI_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) intro_vpl_append sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) change_vpl_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.ghostI_u f ()    in
      (**) let sl1'   = gget_f (G.reveal post x) in
      (**) change_vpl_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) elim_vpl_append (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      Steel.Effect.Atomic.return x)

inline_for_extraction noextract
let spec_r_of_find_ro__ghost
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a)) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : G.erased (spec_find_ro a pre post req ens))
      (#opened : Mem.inames) (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : spc_steel_t (SH.KGhost opened) sro.sro_spc
  = SH.ghost_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) intro_vpl_append sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) change_vpl_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.ghost_u f ()    in
      (**) let sl1'   = gget_f (G.reveal post x) in
      (**) change_vpl_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) elim_vpl_append (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      noop ();
      x)

#pop-options

inline_for_extraction noextract
let spec_r_of_find_ro
      (#a : Type) (#pre : G.erased pre_t) (#post : G.erased (post_t a)) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : G.erased (spec_find_ro a pre post req ens))
      (#ek : SH.effect_kind) (f : repr_steel_t ek a pre post req ens)
  : spc_steel_t ek sro.sro_spc
  = match ek with
  | SH.KSteel    -> spec_r_of_find_ro__steel  sro f
  | SH.KAtomic o -> spec_r_of_find_ro__atomic sro #o f
  | SH.KGhostI o -> spec_r_of_find_ro__ghostI sro #o f
  | SH.KGhost  o -> spec_r_of_find_ro__ghost  sro #o f

(**) private let __end_spec_r_of_find_ro = ()
