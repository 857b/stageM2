module Experiment.Steel.Repr.M

module T = FStar.Tactics
module L = FStar.List.Pure

#set-options "--ide_id_info_off"

(*** [repr_steel_t] *)

let steel_of_repr_lem #a #pre #post #req #ens (tr : to_repr_t a pre post req ens)
  : Lemma (pre `equiv` vprop_of_list tr.r_pre /\
           pre `can_be_split` vprop_of_list tr.r_pre /\
           (forall (x : a) . can_be_split (post x) (vprop_of_list (tr.r_post x))))
  =
    tr.r_pre_eq ();
    equiv_can_be_split pre (vprop_of_list tr.r_pre);
    introduce forall (x : a) . can_be_split (post x) (vprop_of_list (tr.r_post x))
      with (tr.r_post_eq x;
            equiv_can_be_split (post x) (vprop_of_list (tr.r_post x)))

inline_for_extraction noextract
let steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : SH.unit_steel a pre post req ens
  =
    (**) steel_of_repr_lem tr;
    (**) FStar.Classical.forall_intro tr.r_req_eq;
    (**) FStar.Classical.forall_intro_3 tr.r_ens_eq;
    SH.unit_steel_subcomp_no_frame
      _ _ req ens
      (tr.r_pre_eq ()) (fun x -> tr.r_post_eq x)
      ()
      (SH.steel_u f)

let repr_steel_of_steel_lem #a #pre #post #req #ens (tr : to_repr_t a pre post req ens)
  : Lemma (vprop_of_list tr.r_pre `equiv` pre /\
           (forall (x : a) . vprop_of_list (tr.r_post x) `equiv` post x))
  =
    tr.r_pre_eq (); equiv_sym pre (vprop_of_list tr.r_pre);
    introduce forall (x : a) . vprop_of_list (tr.r_post x) `equiv` post x
      with (tr.r_post_eq x; equiv_sym (post x) (vprop_of_list (tr.r_post x)))

inline_for_extraction noextract
let repr_steel_of_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel a pre post req ens)
  : repr_steel_t SH.KSteel a tr.r_pre tr.r_post tr.r_req tr.r_ens
  =
    (**) steel_of_repr_lem tr;
    (**) repr_steel_of_steel_lem tr;
    (**) FStar.Classical.forall_intro tr.r_req_eq;
    (**) FStar.Classical.forall_intro_3 tr.r_ens_eq;
    SH.steel_f (SH.unit_steel_subcomp_no_frame
      req ens _ _
      () (fun _ -> ())
      (SH.intro_subcomp_no_frame_pre _ _ _ _ _ _
        (fun h0 -> tr.r_req_eq (focus_rmem h0 pre))
        (fun h0 x h1 -> tr.r_ens_eq (focus_rmem h0 pre) x (focus_rmem h1 (post x))))
      f)

inline_for_extraction noextract
let steel_ghost_of_repr
      #a #opened (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      f
  =
    (**) steel_of_repr_lem tr;
    (**) FStar.Classical.forall_intro tr.r_req_eq;
    (**) FStar.Classical.forall_intro_3 tr.r_ens_eq;
    SH.unit_steel_ghost_subcomp_no_frame #a #opened
      _ _ req ens
      (tr.r_pre_eq ()) (fun x -> tr.r_post_eq x)
      ()
      (SH.ghost_u f)

inline_for_extraction noextract
let repr_steel_of_steel_ghost
      #a #opened (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      ($f  : SH.unit_steel_ghost a opened pre post req ens)
  : repr_steel_t (SH.KGhost opened) a tr.r_pre tr.r_post tr.r_req tr.r_ens
  =
    (**) steel_of_repr_lem tr;
    (**) repr_steel_of_steel_lem tr;
    (**) FStar.Classical.forall_intro tr.r_req_eq;
    (**) FStar.Classical.forall_intro_3 tr.r_ens_eq;
    SH.ghost_f #opened (SH.unit_steel_ghost_subcomp_no_frame
      req ens _ _
      () (fun _ -> ())
      (SH.intro_subcomp_no_frame_pre _ _ _ _ _ _
        (fun h0 -> tr.r_req_eq (focus_rmem h0 pre))
        (fun h0 x h1 -> tr.r_ens_eq (focus_rmem h0 pre) x (focus_rmem h1 (post x))))
      f)


#push-options "--ifuel 0 --fuel 0"
inline_for_extraction noextract
let spec_r_of_find_ro
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : spec_find_ro a pre post req ens)
      (f : repr_steel_t SH.KSteel a pre post req ens)
  : spc_steel_t SH.KSteel sro.sro_spc
  = SH.steel_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) steel_intro_vprop_of_list_append_f sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) steel_change_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.steel_u f ()     in
      (**) let sl1'   = gget_f (post x) in
      (**) steel_change_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) steel_elim_vprop_of_list_append_f (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      Steel.Effect.Atomic.return x
    )

inline_for_extraction noextract
let spec_r_of_find_ro_ghost
      (#a : Type) (#pre : pre_t) (#post : post_t a) (#req : req_t pre) (#ens : ens_t pre a post)
      (sro : spec_find_ro a pre post req ens)
      (#opened : Mem.inames) (f : repr_steel_t (SH.KGhost opened) a pre post req ens)
  : spc_steel_t (SH.KGhost opened) sro.sro_spc
  = SH.ghost_f (fun () ->
      (**) let sl0    = gget_f sro.sro_spc.spc_pre in
      (**) let sl_fr0 = gget_f sro.sro_spc.spc_ro  in
      (**) steel_intro_vprop_of_list_append_f sro.sro_spc.spc_pre sro.sro_spc.spc_ro;
      (**) steel_change_perm sro.sro_pre_eq;
      (**) sro.sro_req_eq sl0 sl_fr0;
      let (x : a) = SH.ghost_u f ()     in
      (**) let sl1'   = gget_f (post x) in
      (**) steel_change_perm (sro.sro_post_eq x);
      (**) extract_vars_sym_l (sro.sro_post_eq x) sl1';
      (**) steel_elim_vprop_of_list_append_f (sro.sro_spc.spc_post x) sro.sro_spc.spc_ro;
      (**) let sl1    = gget_f (sro.sro_spc.spc_post x) in
      (**) let sl_fr1 = gget_f sro.sro_spc.spc_ro       in
      (**) sro.sro_ens_eq sl0 sl_fr0 x sl1 sl_fr1;
      noop ();
      x
    )
#pop-options

(**) private let __end_spec_r_of_find_ro = ()
