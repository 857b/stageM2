module Experiment.Steel

/// Entry point for the functionalisation of Steel programs

module U    = Learn.Util
module L    = FStar.List.Pure
module SE   = Steel.Effect
module SH   = Experiment.Steel.SteelHack
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module Perm = Learn.Permutation

module M   = Experiment.Steel.Repr.M
module ST  = Experiment.Steel.Repr.ST
module SF  = Experiment.Steel.Repr.SF
module Fun = Experiment.Repr.Fun
module CSl = Experiment.Steel.CondSolver
module ST2SF_Spec = Experiment.Steel.Repr.ST_to_SF.Spec
module ST2SF_Base = Experiment.Steel.Repr.ST_to_SF.Base

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Interface

#push-options "--ifuel 0"
(**) private val __begin_prog_M_to_Fun : unit

let prog_M_to_Fun
      (opt : prog_M_to_Fun_opt)
      (#ek : SH.effect_kind) (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
  : (sl0 : M.sl_f pre) ->
    Fun.prog_tree #SF.sl_tys SF.({val_t = a; sel_t = ST.post_ST_of_M post})
  =
    let { pc_tree = t_M; pc_post_len = post_n; pc_shape = shp_M } = c in
    let t_ST    = ST.repr_ST_of_M t.repr_tree t_M   in
    let shp_ST  = ST.shape_ST_of_M shp_M            in
    (**) ST.repr_ST_of_M_shape t.repr_tree t_M shp_M;
    let (|t_ST', shp_ST'|)
      : (t : ST.prog_tree a _ _ & s : ST.shape_tree _ _ {ST.prog_has_shape t s}) =
      if opt.o_flatten
      then ((**) ST.flatten_prog_shape t_ST shp_ST;
           (|ST.flatten_prog t_ST, ST.flatten_shape shp_ST|))
      else (|t_ST, shp_ST|)                         in
    begin fun (sl0 : M.sl_f pre) ->
      let (|t_SF, shp_SF|)
        : (t : SF.prog_tree a _ & s : SF.shape_tree _ {SF.prog_has_shape t s})
        = if opt.o_ST2SF then (
             let s_ST' = ST.mk_prog_shape t_ST' shp_ST' in
             (**) ST2SF_Spec.repr_SF_of_ST_shape t_ST' s_ST' sl0;
             (|ST2SF_Spec.repr_SF_of_ST_rall t_ST' s_ST' sl0, ST2SF_Spec.shape_SF_of_ST_rall shp_ST'|)
          ) else (
             (**) ST2SF_Base.repr_SF_of_ST_shape t_ST' shp_ST' sl0;
             (|ST2SF_Base.repr_SF_of_ST t_ST' sl0, ST2SF_Base.shape_SF_of_ST shp_ST'|)
          )
      in
      let t_Fun   = SF.repr_Fun_of_SF t_SF    in
      let shp_Fun = SF.shape_Fun_of_SF shp_SF in
      (**) SF.repr_Fun_of_SF_shape t_SF (SF.mk_prog_shape t_SF shp_SF);
      if opt.o_elim_ret
      then Fun.elim_returns SF.sl_tys_lam t_Fun shp_Fun
      else t_Fun
    end

#pop-options
(**) private val __end_prog_M_to_Fun : unit

val prog_M_to_Fun_equiv
      (opt : prog_M_to_Fun_opt)
      (#ek : SH.effect_kind) (#a : Type) (t : M.repr ek a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_f pre)
  : Lemma (M.tree_req t.repr_tree c.pc_tree sl0 <==> Fun.tree_req (prog_M_to_Fun opt t c sl0) /\
          (M.tree_req t.repr_tree c.pc_tree sl0 ==>
          (forall (x : a) (sl1 : M.sl_f (post x)) .
               (M.tree_ens t.repr_tree c.pc_tree sl0 x sl1 <==>
                Fun.tree_ens (prog_M_to_Fun opt t c sl0) SF.({val_v = x; sel_v = sl1})))))

inline_for_extraction
let prog_M_to_Fun_extract
      (opt : prog_M_to_Fun_opt)
      (#a : Type) (t : M.repr SH.KSteel a)
      (#pre : Ghost.erased M.pre_t) (#post : Ghost.erased (M.post_t a))
      (c : Ghost.erased (M.prog_cond t.repr_tree pre post))
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sub : (sl0 : M.sl_f pre) -> Lemma (requires req sl0)
               (ensures Fun.tree_req (prog_M_to_Fun opt t c sl0) /\
                  (forall (x : a) (sl1 : M.sl_f (Ghost.reveal post x)) .
                    Fun.tree_ens (prog_M_to_Fun opt t c sl0) SF.({val_v = x; sel_v = sl1}) ==>
                    ens sl0 x sl1)))
  : M.repr_steel_t SH.KSteel a pre post req ens
  =
    M.repr_steel_subcomp _ _ _ _
      (fun sl0       -> let _ = sub sl0; prog_M_to_Fun_equiv opt t c sl0 in ())
      (fun sl0 x sl1 -> let _ = prog_M_to_Fun_equiv opt t c sl0; sub sl0 in ())
      (t.repr_steel pre post M.(c.pc_tree))


inline_for_extraction
let prog_M_to_Fun_extract_wp
      (opt : prog_M_to_Fun_opt)
      (#a : Type) (t : M.repr SH.KSteel a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : Ghost.erased (M.prog_cond t.repr_tree pre post))
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (wp : (sl0 : M.sl_f pre) -> Lemma
              (requires req sl0)
              (ensures Fun.tree_wp (prog_M_to_Fun opt t c sl0) (fun res -> ens sl0 res.val_v res.sel_v)))
  : M.repr_steel_t SH.KSteel a pre post req ens
  = prog_M_to_Fun_extract opt t c req ens
      (fun sl0 -> wp sl0;
               Fun.tree_wp_sound (prog_M_to_Fun opt t c sl0) (fun res -> ens sl0 res.val_v res.sel_v))


(**** normalisation steps *)

let __normal_M : list norm_step = [
  delta_only [`%M.vprop_list_sels_t;     `%M.Mkrepr?.repr_tree;
              `%M.Mkprog_cond?.pc_tree;  `%M.Mkprog_cond?.pc_post_len; `%M.Mkprog_cond?.pc_shape;
              `%L.map; `%SE.Mkvprop'?.t;
              `%prog_M_to_Fun];
  delta_attr [`%__tac_helper__; `%M.__repr_M__;
              `%SE.__steel_reduce__; `%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

let __normal_ST : list norm_step = [
  delta_only [`%ST.repr_ST_of_M; `%ST.repr_ST_of_M_Spec; `%ST.bind; `%ST.post_ST_of_M;
              `%M.vprop_list_sels_t; `%L.map; `%SE.Mkvprop'?.t;
              `%ST.const_post; `%ST.frame_post; `%L.op_At; `%L.append;
              `%ST.flatten_prog; `%ST.flatten_prog_aux; `%ST.flatten_prog_k_id;

              `%ST.shape_ST_of_M; `%ST.flatten_shape; `%ST.flatten_shape_aux; `%ST.flatten_shape_k_id;
              `%M.Mkprog_cond?.pc_tree;  `%M.Mkprog_cond?.pc_post_len; `%M.Mkprog_cond?.pc_shape;
              `%Perm.perm_f_to_list; `%Ll.initi; `%Perm.id_n; `%Perm.mk_perm_f];
  delta_qualifier ["unfold"];
  delta_attr [`%__tac_helper__; `%SE.__steel_reduce__];
  iota; zeta; primops
]

let __delta_ST2SF_Spec : list string = ST2SF_Spec.([
  `%repr_SF_of_ST_rall; `%repr_SF_of_ST; `%shape_SF_of_ST;
  `%shape_SF_of_ST_rall;
  `%post_SF_of_ST; `%postl_SF_of_ST; `%post_bij;
  `%Mkpost_bij_t'?.len_SF; `%Mkpost_bij_t'?.idx_SF; `%Mkpost_bij_t'?.idx_ST;
  `%sel_ST_of_SF; `%sell_ST_of_SF; `%post_src_of_shape;
  `%post_src_f_of_shape; `%sel_SF_of_ST; `%sell_SF_of_ST
])

let __delta_ST2SF_Base : list string = ST2SF_Base.([
  `%repr_SF_of_ST; `%shape_SF_of_ST;
  `%L.op_At; `%L.append;
  `%Fl.apply_perm_r; `%Fl.append;
  `%ST.const_post; `%ST.frame_post
])

let __normal_SF : list norm_step = [
  delta_only (L.append __delta_ST2SF_Spec (L.append __delta_ST2SF_Base [
              `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
              `%Ll.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%L.length;
              `%Fl.splitAt_ty; `%Fl.head; `%Fl.tail;
              `%Fl.dlist_of_f; `%Dl.initi; `%Fl.cons; `%Fl.nil;
              `%Mktuple2?._1;`%Mktuple2?._2;
              `%Learn.Option.map;
              `%Perm.perm_f_swap; `%Perm.perm_f_transpose; `%Perm.perm_f_of_pair;
              `%Perm.mk_perm_f; `%Perm.id_n; `%Perm.perm_f_of_list]));
  delta_qualifier ["unfold"];
  delta_attr [`%U.__util_func__];
  iota; zeta; primops
]

let __normal_Fun : list norm_step = [
  delta_only [`%SF.repr_Fun_of_SF;
              `%SF.shape_Fun_of_SF; `%SF.Mkprog_shape?.post_len; `%SF.Mkprog_shape?.shp];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

let __normal_Fun_elim_returns_0 : list norm_step = [
  delta_only [`%Fun.elim_returns; `%Fun.elim_returns_aux; `%Fun.elim_returns_k_trm; `%Fun.elim_returns_k_ret;
              `%SF.sl_tys; `%SF.sl_tys_lam;
              `%Fun.Mktys'?.v_of_r; `%Fun.Mktys'?.r_of_v;
              `%Fun.Mktys_lam'?.lam_prop; `%Fun.Mktys_lam'?.lam_tree;
              `%SF.Mksl_tys_t?.val_t;     `%SF.Mksl_tys_t?.sel_t;
              `%SF.Mksl_tys_v?.val_v;     `%SF.Mksl_tys_v?.sel_v;
              `%SF.Mksl_tys_r?.vl;        `%SF.Mksl_tys_r?.sl;
              `%Fun.Tret?.x;
              `%SF.sl_r_of_v; `%SF.sl_v_of_r;
              `%Fl.cons; `%Fl.nil; `%Fl.dlist_of_f; `%Fl.flist_of_d'; `%Dl.initi; `%Dl.index;
              `%L.length; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi
              ];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

let __normal_Fun_elim_returns_1 : list norm_step = [
  delta_only [`%SF.delayed_sl_uncurrify];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

let __normal_Fun_spec : list norm_step = [
  delta_only [`%Fun.tree_wp; `%Fl.partial_app_flist;
              `%Fun.Mktys'?.all; `%SF.sl_tys; `%SF.sl_all; `%Fl.forall_flist;
              `%Fun.Mktys'?.v_of_r; `%SF.sl_v_of_r; `%Fl.flist_of_d';
              `%Fl.cons; `%Fl.nil;
              `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t;
              `%SF.Mksl_tys_v?.val_v; `%SF.Mksl_tys_v?.sel_v;
              `%SF.Mksl_tys_r?.vl; `%SF.Mksl_tys_r?.sl];
  delta_qualifier ["unfold"];
  delta_attr [`%SE.__steel_reduce__];
  iota; zeta; primops
]

let __normal_vprop_list : list norm_step = [
  delta_only [`%M.vprop_of_list; `%M.vprop_list_sels_t; `%M.sel_f'; `%M.sel';
              `%Fl.flist_of_g; `%Fl.dlist_of_f_g; `%Fl.flist_of_d;
              `%Dl.index; `%Dl.initi_g;
              `%L.length; `%L.index; `%L.map; `%L.hd; `%L.tl; `%L.tail];
  delta_attr [`%SE.__reduce__];
  iota; zeta; primops
]


(***** Calling a [M.repr_steel_t] from a Steel program *)

unfold
let norm_vpl (#a : Type) (x : a) = Pervasives.norm __normal_vprop_list x

inline_for_extraction
val call_repr_steel
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t SH.KSteel a pre post req ens)
  : SE.Steel a (M.vprop_of_list' pre) (fun x -> M.vprop_of_list' (post x))
      (requires fun h0      -> norm_vpl (req (M.sel_f' pre h0)))
      (ensures  fun h0 x h1 -> norm_vpl (ens (M.sel_f' pre h0) x (M.sel_f' (post x) h1)))


(***** Extracting a [M.repr_steel_t] from a [M.repr] *)

/// We mention [t] so that it is specified by the goal, but this type is just a synonym for [M.repr_steel_t].
let extract (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
            (t : M.repr SH.KSteel a)
  : Type
  = M.repr_steel_t SH.KSteel a pre post req ens

[@@ erasable]
noeq
type solve_by_wp_ghost
       (opt : prog_M_to_Fun_opt)
       (a : Type) (t : M.repr SH.KSteel a)
       (pre : M.pre_t) (post : M.post_t a)
       (req : M.req_t pre) (ens : M.ens_t pre a post)
= {
  s_cond   : M.prog_cond t.repr_tree pre post;
  s_Fun    : (sl0 : M.sl_f pre) -> GTot (Fun.prog_tree #SF.sl_tys SF.({val_t = a; sel_t = ST.post_ST_of_M post}));
  s_Fun_eq : squash (s_Fun == (fun sl0 -> prog_M_to_Fun opt t s_cond sl0));
  s_wp     : squash (Fl.forall_flist (M.vprop_list_sels_t pre) (fun sl0 ->
               req sl0 ==>
               Fun.tree_wp (s_Fun sl0) (fun res -> ens sl0 res.val_v res.sel_v)))
}

[@@ __tac_helper__]
inline_for_extraction
let __solve_by_wp
      (opt : prog_M_to_Fun_opt)
      (#a : Type) (#t : M.repr SH.KSteel a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (sol : squash (solve_by_wp_ghost opt a t pre post req ens))
  : extract a pre post req ens t
  =
    // We use indefinite descriptors to force the erasure of the ghost parts
    let sol_v = FStar.IndefiniteDescription.elim_squash sol in
    prog_M_to_Fun_extract_wp opt t sol_v.s_cond req ens (fun sl0 -> ())


/// Solves a goal of the form [extract a pre post req ens t]
let solve_by_wp (fr : flags_record) : Tac unit
  =
    let opt   = fr.o_M2Fun      in
    let u_sol = fresh_uvar None in
    let u_cond     = fresh_uvar None in
    let u_t_Fun    = fresh_uvar None in
    let u_t_Fun_eq = fresh_uvar None in
    let u_wp       = fresh_uvar None in
    apply_raw (`(__solve_by_wp (`#(quote opt)) (`#u_sol)));
    unshelve u_sol;
    squash_intro ();
    apply_raw (`(Mksolve_by_wp_ghost (`#u_cond) (`#u_t_Fun) (`#u_t_Fun_eq) (`#u_wp)));

    let t = timer_start   "prog_cond " fr.f_timer in
    (* cond *)
    unshelve u_cond;
    norm __normal_M;
    CSl.build_prog_cond fr;

    (* t_Fun *)
    unshelve u_t_Fun_eq;
    (* TODO? stage prog_M_to_Fun to avoid duplication *)
    let t = timer_enter t "normal_M  " in
    norm __normal_M;
    if fr.f_dump Stage_M then dump "at stage M";
    let t = timer_enter t "normal_ST " in
    norm __normal_ST;
    if fr.f_dump Stage_ST then dump "at stage ST";
    let t = timer_enter t "normal_SF " in
    norm __normal_SF;
    if fr.f_dump Stage_SF then dump "at stage SF";
    let t = timer_enter t "normal_Fun" in
    norm __normal_Fun;
    if opt.o_elim_ret then begin
      norm __normal_Fun_elim_returns_0;
      norm __normal_Fun_elim_returns_1
    end;
    if fr.f_dump Stage_Fun then dump "at stage Fun";
    let t = timer_enter t "misc      " in
    trefl ();

    (* wp *)
    let t = timer_enter t "Fun_wp    " in
    unshelve u_wp;
    norm __normal_M;
    norm __normal_Fun_spec;
    if fr.f_dump Stage_WP then dump "at stage WP";
    smt ();

    timer_stop t


(***** Extracting a [unit_steel] from a [M.repr] *)

/// Similarly to [extract], [t] is only mentioned so that it can be retrieved by the tactic
type __to_steel_goal
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : M.repr SH.KSteel a)
  = SH.unit_steel a pre post req ens

[@@ __tac_helper__]
inline_for_extraction
let __build_to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#t : M.repr SH.KSteel a)
      (goal_tr : Ghost.erased (M.to_repr_t a pre post req ens))
      (goal_f  : M.(extract a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens) t)
  : __to_steel_goal a pre post req ens t
  = M.steel_of_repr goal_tr goal_f

/// Solves a goal [__to_steel_goal]
// FIXME: this tactic get stuck if this file is lax-checked
let build_to_steel (fr : flags_record) : Tac unit
  =
    // This tactics fails if called in lax mode.
    // It appears that at this point the goal contains unification variables in lax-mode:
    //   __to_steel_goal unit ?pre ?post ?req ?ens t
    // whereas the specifications are concrete terms (inferred from the top-level annotation) in normal-mode.
    // If we try to solve the goal with [lax_guard], Steel then fails to solve some [equiv] with the
    // [__lax_made] introduced for the specifications.
    
    let t = timer_start "specs     " fr.f_timer in
    apply_raw (`__build_to_steel);
    apply_raw (`Ghost.hide);
    CSl.build_to_repr_t fr (fun () -> [Info_location "in the specification"]);
    timer_stop t;

    // [extract]
    norm [delta_attr [`%__tac_helper__]; iota];
    solve_by_wp fr


[@@ __tac_helper__]
inline_for_extraction
let to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (t : M.repr SH.KSteel a)
      (g : __to_steel_goal a pre post req ens t)
  : SH.unit_steel a pre post req ens
  = g
