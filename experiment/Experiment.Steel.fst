module Experiment.Steel

/// Entry point for the functionalisation of Steel programs

module U    = Learn.Util
module L    = FStar.List.Pure
module SE   = Steel.Effect
module SH   = Experiment.Steel.Steel
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module UV   = Learn.Universe
module Msk  = Learn.List.Mask
module Mem  = Steel.Memory
module Perm = Learn.Permutation

module M   = Experiment.Steel.Repr.M
module ST  = Experiment.Steel.Repr.ST
module LV  = Experiment.Steel.Repr.LV
module SF  = Experiment.Steel.Repr.SF
module Fun = Experiment.Repr.Fun
module Vpl = Experiment.Steel.VPropList
module Veq = Experiment.Steel.VEquiv

module TcS  = Experiment.Steel.Tac
module TcM  = Experiment.Steel.Tac.MCond
module TcLV = Experiment.Steel.Tac.LV

module LV2M   = Experiment.Steel.Repr.LV_to_M
module LV2SF  = Experiment.Steel.Repr.LV_to_SF
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Interface


/// Here, [lc] should be the [lin_cond] obtained from [LV.lc_sub_push]
let prog_LV_to_Fun
      (#a : Type) (t : M.prog_tree a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (lc : LV.top_lin_cond t pre post)
      (sl0 : Vpl.sl_f pre)
  : Fun.prog_tree #SF2Fun.sl_tys SF.({val_t = a; sel_t = M.post_sl_t post})
  =
    let t_SF = LV2SF.repr_SF_of_LV lc (Fl.dlist_of_f sl0) in
    SF2Fun.repr_Fun_of_SF t_SF

let prog_M_equiv_Fun 
      (#a : Type) (t : M.prog_tree a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.tree_cond t pre post)
      (sl0 : Vpl.sl_f pre)
      (f : Fun.prog_tree #SF2Fun.sl_tys SF.({val_t = a; sel_t = M.post_sl_t post}))
  : prop
  = (M.tree_req t c sl0 <==> Fun.tree_req f) /\
    (M.tree_req t c sl0 ==>
    (forall (x : a) (sl1 : Vpl.sl_f (post x)) .
        M.tree_ens t c sl0 x sl1 <==> Fun.tree_ens f ({val_v = x; sel_v = sl1})))

#push-options "--ifuel 0 --fuel 0"
let prog_LV_to_Fun_equiv_M
      (#a : Type) (t : M.prog_tree a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (lc : LV.top_lin_cond t pre post {LV.lcsub_at_leaves lc})
      (sl0 : Vpl.sl_f pre)
  : Lemma (prog_M_equiv_Fun t (LV2M.repr_M_of_LV_top lc) sl0 (prog_LV_to_Fun t lc sl0))
  =
    let mc    = LV2M.repr_M_of_LV_top lc     in
    let sl0_l = Fl.dlist_of_f sl0            in
    let t_SF  = LV2SF.repr_SF_of_LV lc sl0_l in
    let t_Fun = prog_LV_to_Fun t lc sl0      in

    LV2M.repr_M_of_LV_top_sound lc;
    LV2SF.repr_SF_of_LV_sound lc sl0_l;
    SF2Fun.repr_Fun_of_SF_req t_SF;

    let lem_req () : Lemma (M.tree_req t mc sl0 <==> Fun.tree_req t_Fun) = () in
    let lem_ens (x : a) (sl1 : Vpl.sl_f (post x))
      : Lemma (M.tree_ens t mc sl0 x sl1 <==> Fun.tree_ens t_Fun ({val_v = x; sel_v = sl1}))
      = SF2Fun.repr_Fun_of_SF_ens t_SF x sl1
    in
    assert (prog_M_equiv_Fun t (LV2M.repr_M_of_LV_top lc) sl0 (prog_LV_to_Fun t lc sl0))
      by (norm [delta_only [`%prog_M_equiv_Fun]];
          split ();
            apply_lemma (``@lem_req);
            let _ = mintros () in apply_lemma (``@lem_ens))
#pop-options

[@@ __extraction__]
inline_for_extraction
let prog_LV_to_Fun_extract
      (#ek : SH.effect_kind) (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (lc : LV.top_lin_cond t.repr_tree pre post {LV.lcsub_at_leaves lc})
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sub : (sl0 : Vpl.sl_f pre) -> Lemma (requires req sl0)
               (ensures Fun.tree_req (prog_LV_to_Fun t.repr_tree lc sl0) /\
                  (forall (x : a) (sl1 : Vpl.sl_f (post x)) .
                    Fun.tree_ens (prog_LV_to_Fun t.repr_tree lc sl0) SF.({val_v = x; sel_v = sl1}) ==>
                    ens sl0 x sl1)))
  : M.repr_steel_t ek a pre post req ens
  =
    let tr = t.repr_tree in
    let mc = LV2M.repr_M_of_LV_top lc in
    U.cast _ (M.repr_steel_subcomp ek #a #pre #post (M.tree_req _ mc) (M.tree_ens _ mc) req ens
      (fun sl0       -> let _ =
        let f = prog_LV_to_Fun t.repr_tree lc sl0 in
        sub sl0;
        prog_LV_to_Fun_equiv_M t.repr_tree lc sl0;
        // Probably because of [U.eta], the SMT fails to solve this. We rely on tactics instead.
        assert (prog_M_equiv_Fun tr mc sl0 f ==> (M.tree_req tr mc sl0 <==> Fun.tree_req f))
          by (hyp (destruct_and (implies_intro ()))._1)
        in ())
      (fun sl0 x sl1 -> let _ =
        let f = prog_LV_to_Fun t.repr_tree lc sl0 in
        prog_LV_to_Fun_equiv_M t.repr_tree lc sl0;
        assert (prog_M_equiv_Fun tr mc sl0 f ==> M.tree_req tr mc sl0 ==>
          (M.tree_ens tr mc sl0 x sl1 <==> Fun.tree_ens f ({val_v = x; sel_v = sl1})))
          by (let eqv = (destruct_and (implies_intro ()))._2 in
              let req = implies_intro () in
              let eqv = instantiate (binder_to_term eqv) (binder_to_term req) in
              let eqv = instantiate (binder_to_term eqv) (``@x) in
              let eqv = instantiate (binder_to_term eqv) (``@sl1) in
              hyp eqv);
        sub sl0
        in ())
      (t.repr_steel pre (U.eta post) mc))

#push-options "--ifuel 0 --fuel 0"
[@@ __extraction__]
inline_for_extraction
let prog_LV_to_Fun_extract_wp
      (#ek : SH.effect_kind) (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (lc0 : LV.top_lin_cond t.repr_tree pre post)
      (lc1 : LV.top_lin_cond t.repr_tree pre post) (_ : squash (lc1 == LV.lc_sub_push lc0))
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (wp : (sl0 : Vpl.sl_f pre) -> Lemma
              (requires req sl0)
              (ensures Fun.tree_wp (prog_LV_to_Fun t.repr_tree lc1 sl0) (fun res -> ens sl0 res.val_v res.sel_v)))
  : M.repr_steel_t ek a pre post req ens
  =
    (**) LV.lc_sub_push_at_leaves _ lc0;
    prog_LV_to_Fun_extract t lc1 req ens
      (fun sl0 -> wp sl0;
               Fun.tree_wp_sound (prog_LV_to_Fun t.repr_tree lc1 sl0) (fun res -> ens sl0 res.val_v res.sel_v))
#pop-options


(**** normalisation steps *)

let __normal_M : list norm_step = [
  delta_only [`%Vpl.vprop_list_sels_t;   `%M.Mkrepr?.repr_tree;
              `%L.map; `%SE.Mkvprop'?.t; `%UV.lift_dom];
  delta_attr [`%__tac_helper__; `%__repr_M__; `%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; unascribe
]

let __normal_lc_sub_push : list norm_step = [
  delta_only (L.append TcS.__delta_list
             [`%LV.lc_sub_push; `%LV.lc_sub_push_aux; `%LV.lcsubp_tr;
              `%Perm.perm_f_to_list; `%Perm.perm_f_of_list;
              `%Perm.comp; `%Perm.mk_perm_f; `%Perm.perm_f_append; `%Perm.perm_f_cons; `%Perm.id_n;
              `%Perm.perm_f_cons_snoc]);
  delta_attr [`%LV.__lin_cond__; `%Msk.__mask__; `%__tac_helper__];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]

let __normal_LV2SF : list norm_step = [
  delta_only [`%prog_LV_to_Fun; `%LV2SF.repr_SF_of_LV;
              `%Vpl.filter_sl;
              `%M.post_sl_t; `%Vpl.vprop_list_sels_t;
              `%L.map; `%L.op_At; `%L.append; `%Ll.initi; `%L.length; `%Ll.repeat;
              `%Dl.initi; `%Dl.append; `%Dl.index; `%Dl.dlist_eq2; `%Msk.dl_append_on_mask;
              `%Fl.dlist_of_f; `%Fl.flist_eq2;
              `%Fl.append; `%Fl.splitAt_ty;
              `%Mktuple2?._1; `%Mktuple2?._2;
              `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t];
  delta_attr [`%__LV2SF__; `%LV.__lin_cond__; `%Msk.__mask__; `%__tac_helper__; `%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]

let __normal_Fun : list norm_step = [
  delta_only [`%SF2Fun.repr_Fun_of_SF;
              `%SF2Fun.shape_Fun_of_SF; `%SF.Mkprog_shape?.post_len; `%SF.Mkprog_shape?.shp];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]

let __normal_Fun_elim_returns_0 : list norm_step = [
  delta_only [`%Fun.elim_returns; `%Fun.elim_returns_aux; `%Fun.elim_returns_k_trm; `%Fun.elim_returns_k_ret;
              `%SF2Fun.sl_tys; `%SF2Fun.sl_tys_lam;
              `%Fun.Mktys'?.v_of_r; `%Fun.Mktys'?.r_of_v;
              `%Fun.Mktys_lam'?.lam_prop; `%Fun.Mktys_lam'?.lam_tree;
              `%SF.Mksl_tys_t?.val_t;     `%SF.Mksl_tys_t?.sel_t;
              `%SF.Mksl_tys_v?.val_v;     `%SF.Mksl_tys_v?.sel_v;
              `%SF2Fun.Mksl_tys_r?.vl;    `%SF2Fun.Mksl_tys_r?.sl;
              `%Fun.Tret?.x;
              `%SF2Fun.sl_r_of_v; `%SF2Fun.sl_v_of_r;
              `%Fl.cons; `%Fl.nil; `%Fl.dlist_of_f; `%Fl.flist_of_d'; `%Dl.initi; `%Dl.index;
              `%L.length; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi
              ];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]

let __normal_Fun_elim_returns_1 : list norm_step = [
  delta_only [`%SF2Fun.delayed_sl_uncurrify];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]

let __normal_Fun_spec : list norm_step = [
  delta_only [`%Fun.tree_wp; `%Fl.partial_app_flist;
              `%Fun.Mktys'?.all; `%SF2Fun.sl_tys; `%SF2Fun.sl_all; `%Fl.forall_flist;
              `%Fun.Mktys'?.v_of_r; `%SF2Fun.sl_v_of_r; `%Fl.flist_of_d';
              `%Fl.cons; `%Fl.nil;
              `%SF.Mksl_tys_t?.val_t;  `%SF.Mksl_tys_t?.sel_t;
              `%SF.Mksl_tys_v?.val_v;  `%SF.Mksl_tys_v?.sel_v;
              `%SF2Fun.Mksl_tys_r?.vl; `%SF2Fun.Mksl_tys_r?.sl;
              `%Vpl.vprop_of_list; `%Vpl.vprop_of_list'];
  delta_qualifier ["unfold"];
  delta_attr [`%SE.__steel_reduce__; `%Msk.__mask__; `%UV.__universe__];
  iota; zeta; primops; unascribe
]

let __normal_vprop_list : list norm_step = [
  delta_only [`%Vpl.vprop_of_list; `%Vpl.vprop_list_sels_t;
              `%Fl.flist_of_g; `%Fl.dlist_of_f_g; `%Fl.flist_of_d;
              `%Dl.index; `%Dl.initi_g;
              `%L.length; `%L.index; `%L.map; `%L.hd; `%L.tl; `%L.tail];
  delta_attr [`%SE.__reduce__];
  iota; zeta; primops; unascribe
]

let __normal_extract : list norm_step = [
  delta_attr [`%__repr_M__; `%__extraction__];
  delta_qualifier ["unfold"];
  iota; zeta; primops; unascribe
]


(***** Extracting a [M.repr_steel_t] from a [M.repr] *)

/// We mention [t] so that it is specified by the goal, but this type is just a synonym for [M.repr_steel_t].
let extract (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
            (ek : SH.effect_kind) (t : M.repr ek a)
  : Type
  = M.repr_steel_t ek a pre post req ens

[@@ __tac_helper__; __extraction__]
inline_for_extraction
let __solve_by_wp_LV
      (#ek : SH.effect_kind) (#a : Type) (r : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (#t : M.prog_tree a) (_ : squash (t == r.repr_tree))
      (lc0 : LV.top_lin_cond t pre post)
      (lc1 : LV.top_lin_cond t pre post) (lc1_eq : squash (lc1 == LV.lc_sub_push lc0))
      (t_Fun : (sl0 : Vpl.sl_f pre) ->
               GTot (Fun.prog_tree #SF2Fun.sl_tys ({val_t = a; sel_t = M.post_sl_t post})))
      (t_Fun_eq : squash (t_Fun == (fun sl0 -> prog_LV_to_Fun t lc1 sl0)))
      (wp : squash (Fl.forall_flist (Vpl.vprop_list_sels_t pre) (fun sl0 ->
               req sl0 ==>
               Fun.tree_wp (t_Fun sl0) (fun res -> ens sl0 res.val_v res.sel_v))))
      (ext : M.repr_steel_t ek a pre post req ens)
      (ext_eq : ext == prog_LV_to_Fun_extract_wp r lc0 lc1 lc1_eq req ens (fun sl0 -> ()))
  : extract a pre post req ens ek r
  =
    ext

/// Solves a goal of the form [extract a pre post req ens t]
let solve_by_wp (fr : flags_record) (t : timer) : Tac unit
  =
    apply_raw (`__solve_by_wp_LV);

    (* t *)
    dismiss ();
    let t = timer_enter t "M         " in
    norm __normal_M;
    if fr.f_dump Stage_M then dump1 "at stage M";
    trefl ();

    (* lc0 *)
    let t = timer_enter t "lin_cond  " in
    norm __normal_M;
    TcLV.build_top_lin_cond fr (TcS.root_ctx []);

    (* lc1 *)
    let t = timer_enter t "sub_push  " in
    dismiss ();
    TcLV.norm_lc ();
    if fr.f_dump (Stage_LV false) then dump1 "at stage LV (before sub_push)";
    norm __normal_lc_sub_push;
    if fr.f_dump (Stage_LV  true) then dump1 "at stage LV (after sub_push)";
    trefl ();

    (* t_Fun *)
    dismiss ();
    let t = timer_enter t "LV2SF     " in
    norm __normal_LV2SF;
    if fr.f_dump Stage_SF then dump1 "at stage SF";
    let t = timer_enter t "SF2Fun    " in
    norm __normal_Fun;
    if fr.f_dump Stage_Fun then dump1 "at stage Fun";
    trefl ();

    (* wp *)
    let t = timer_enter t "Fun_wp    " in
    norm __normal_M;
    norm __normal_Fun_spec;
    if fr.f_dump Stage_WP then dump1 "at stage WP";
    if fr.f_dump Side_Conditions
    then begin
      let gs = goals () in
      set_goals [];
      dump "side conditions";
      set_goals gs
    end;
    smt ();

    (* ext *)
    dismiss ();
    let t = if fr.f_extr then begin
      // We normalize the resulting Steel program so that it can be extracted
      let t = timer_enter t "extract   " in
      norm __normal_extract;
      // FIXME: [test_for_loop0] fails if one tries to include this in __normal_extract
      // it is only used by [GCombinators.for_loop_cond]
      norm [delta_attr [`%__extraction_fix__]];
      norm __normal_extract;
      t
    end else t in
    if fr.f_dump Stage_Extract then dump1 "at stage Extract";
    trefl ();
    timer_stop t



(***** Extracting a [unit_steel] from a [M.repr] *)

/// Similarly to [extract], [t] is only mentioned so that it can be retrieved by the tactic
type __to_steel_goal
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (ek : SH.effect_kind) (t : M.repr ek a)
  = SH.steel a pre post req ens ek

[@@ __tac_helper__]
inline_for_extraction
let __build_to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#ek : SH.effect_kind) (#t : M.repr ek a)
      (goal_tr : M.to_repr_t a pre post req ens)
      (goal_f  : extract a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens ek t)
  : __to_steel_goal a pre post req ens ek t
  = M.steel_of_repr goal_tr goal_f

/// Solves a goal [__to_steel_goal]
let build_to_steel (fr : flags_record) : Tac unit
  =
    // This tactics fails if called in lax mode.
    // It appears that at this point the goal contains unification variables in lax-mode:
    //   __to_steel_goal unit ?pre ?post ?req ?ens t
    // whereas the specifications are concrete terms (inferred from the top-level annotation) in normal-mode.
    // If we try to solve the goal with [lax_guard], we obtain:
    //   (Error 217) Tactic left uninstantiated unification variable ?421 of type Type
    //               (reason = "Instantiating implicit argument in application")
    with_policy Force (fun () ->
    let t = timer_start "specs     " fr.f_timer in
    apply_raw (`__build_to_steel);
    TcS.build_to_repr_t fr (TcS.root_ctx ["in the specification"]);

    // [extract]
    norm [delta_attr [`%__tac_helper__]; iota];
    solve_by_wp fr t
    )


(***** Using a [rewrite_with_tactic] *)

noeq
type to_steel_goal_spec
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (t : M.prog_tree a)
  = {
    goal_spec_LV : LV.top_lin_cond t pre post;
    goal_spec_WP : squash (
      let lc1 = LV.lc_sub_push goal_spec_LV in
      let t_Fun sl0 = prog_LV_to_Fun t lc1 sl0 in
     (forall (sl0 : Vpl.sl_f pre) .
       req sl0 ==>
       Fun.tree_wp (t_Fun sl0) (fun res -> ens sl0 res.val_v res.sel_v))
    )
  }

let to_steel_goal_spec_WP
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (t : M.prog_tree a)
      (lc0 : LV.top_lin_cond t pre post)
  : Type0
  =
    let lc1 = LV.lc_sub_push lc0 in
    let t_Fun sl0 = prog_LV_to_Fun t lc1 sl0 in
    Fl.forall_flist (Vpl.vprop_list_sels_t pre) (fun (sl0 : Vpl.sl_f pre) ->
       req sl0 ==>
       Fun.tree_wp (t_Fun sl0) (fun res -> ens sl0 res.val_v res.sel_v))

private
let rewrite_to_steel_goal_spec (flags : list flag) () : Tac unit
  =
    let fr = make_flags_record flags in
    norm [delta_only [`%to_steel_goal_spec_WP]];
    
    let t = timer_start "sub_push  " fr.f_timer in
    TcLV.norm_lc ();
    if fr.f_dump (Stage_LV false) then dump1 "at stage LV (before sub_push)";
    norm __normal_lc_sub_push;
    if fr.f_dump (Stage_LV  true) then dump1 "at stage LV (after sub_push)";
    
    let t = timer_enter t "LV2SF     " in
    norm __normal_LV2SF;
    if fr.f_dump Stage_SF then dump1 "at stage SF";
    
    let t = timer_enter t "SF2Fun    " in
    norm __normal_Fun;
    if fr.f_dump Stage_Fun then dump1 "at stage Fun";
    
    let t = timer_enter t "Fun_wp    " in
    norm __normal_M;
    norm __normal_Fun_spec;
    if fr.f_dump Stage_WP then dump1 "at stage WP";

    trefl ();
    timer_stop t

#push-options "--no_tactics"
private
let __build_to_steel_wrew
      (flags : list flag)
      (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
      (t : M.prog_tree a)
      (goal_LV : LV.top_lin_cond t pre post)
      (goal_WP : squash (rewrite_with_tactic (rewrite_to_steel_goal_spec flags)
                         (to_steel_goal_spec_WP a pre post req ens t goal_LV)))
  : to_steel_goal_spec a pre post req ens t
  =
    unfold_rewrite_with_tactic
        (rewrite_to_steel_goal_spec flags)
        (to_steel_goal_spec_WP a pre post req ens t goal_LV);
    Mkto_steel_goal_spec goal_LV goal_WP
#pop-options

let build_to_steel_wrew (fr : flags_record) (ctx : TcS.cs_context) (flags : list flag) (t : timer) : Tac timer
  =
    apply_raw (`__build_to_steel_wrew (`#(quote flags)));
    
    // goal_LV
    let t = timer_enter t "lin_cond  " in
    norm __normal_M;
    if fr.f_dump Stage_M then dump1 "at stage M";
    TcLV.build_top_lin_cond fr ctx;

    if fr.f_dump Side_Conditions
    then begin
      let gs = goals () in
      set_goals [];
      dump "side conditions";
      set_goals gs
    end;

    // goal_WP
    smt ();

    t
