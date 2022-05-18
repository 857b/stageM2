module Experiment.Steel

/// Interface for the functionalisation of Steel programs

module U    = Learn.Util
module L    = FStar.List.Pure
module SE   = Steel.Effect
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module Perm = Learn.Permutation

module M    = Experiment.Steel.Repr.M
module ST   = Experiment.Steel.Repr.ST
module SF   = Experiment.Steel.Repr.SF
module Fun  = Experiment.Repr.Fun
module CSl  = Experiment.Steel.CondSolver

open FStar.Tactics
open Learn.Tactics.Util


let prog_M_to_Fun
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
  : (sl0 : M.sl_t pre) ->
    Fun.prog_tree #SF.sl_tys SF.({val_t = a; sel_t = ST.post_ST_of_M post})
  =
    let { pc_tree = t_M; pc_post_len = post_n; pc_shape = shp_M } = c in
    let t_ST    = ST.repr_ST_of_M t.repr_tree t_M   in
    let shp_ST  = ST.shape_ST_of_M shp_M            in
    (**) ST.repr_ST_of_M_shape t.repr_tree t_M shp_M;
    let t_ST'   = ST.flatten_prog t_ST              in
    let shp_ST' = ST.flatten_shape shp_ST           in
    (**) ST.flatten_prog_shape t_ST shp_ST;
    let s_ST'   = ST.mk_prog_shape t_ST' shp_ST'    in
    begin fun (sl0 : M.sl_t pre) ->
      let t_SF = SF.repr_SF_of_ST_rall t_ST' s_ST' sl0 in
      SF.repr_Fun_of_SF t_SF
    end

val prog_M_to_Fun_equiv
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_t pre)
  : Lemma (M.tree_req t.repr_tree c.pc_tree sl0 <==> Fun.tree_req (prog_M_to_Fun t c sl0) /\
          (M.tree_req t.repr_tree c.pc_tree sl0 ==>
          (forall (x : a) (sl1 : M.sl_t (post x)) .
               (M.tree_ens t.repr_tree c.pc_tree sl0 x sl1 <==>
                Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))))

inline_for_extraction
let prog_M_to_Fun_extract
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sub : (sl0 : M.sl_t pre) -> Lemma (requires req sl0)
               (ensures Fun.tree_req (prog_M_to_Fun t c sl0) /\
                  (forall (x : a) (sl1 : M.sl_t (post x)) .
                    Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1}) ==> ens sl0 x sl1)))
  : M.repr_steel_t a pre post req ens
  =
    M.repr_steel_subcomp _ _ _ _
      (fun sl0       -> let _ = sub sl0; prog_M_to_Fun_equiv t c sl0 in ())
      (fun sl0 x sl1 -> let _ = prog_M_to_Fun_equiv t c sl0; sub sl0 in ())
      (t.repr_steel pre post c.pc_tree)


inline_for_extraction
let prog_M_to_Fun_extract_wp
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (wp : (sl0 : M.sl_t pre) -> Lemma
              (requires req sl0)
              (ensures Fun.tree_wp (prog_M_to_Fun t c sl0) (fun res -> ens sl0 res.val_v res.sel_v)))
  : M.repr_steel_t a pre post req ens
  = prog_M_to_Fun_extract t c req ens
      (fun sl0 -> wp sl0; Fun.tree_wp_sound (prog_M_to_Fun t c sl0) (fun res -> ens sl0 res.val_v res.sel_v))



let __normal_M : list norm_step = [
  delta_only [`%M.vprop_list_sels_t;     `%M.Mkrepr?.repr_tree;
              `%M.Mkprog_cond?.pc_tree;  `%M.Mkprog_cond?.pc_post_len; `%M.Mkprog_cond?.pc_shape;
              `%L.map; `%SE.Mkvprop'?.t;
              `%prog_M_to_Fun];
  delta_attr [`%__tac_helper__; `%M.__repr_M__;
              `%SE.__steel_reduce__; `%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta
]

let __normal_ST : list norm_step = [
  delta_only [`%ST.repr_ST_of_M; `%ST.bind; `%ST.post_ST_of_M;
              `%M.vprop_list_sels_t; `%L.map; `%SE.Mkvprop'?.t;
              `%ST.const_post; `%ST.frame_post; `%L.op_At; `%L.append;
              `%ST.flatten_prog; `%ST.flatten_prog_aux; `%ST.flatten_prog_k_id;

              `%ST.shape_ST_of_M; `%ST.flatten_shape; `%ST.flatten_shape_aux; `%ST.flatten_shape_k_id;
              `%M.Mkprog_cond?.pc_tree;  `%M.Mkprog_cond?.pc_post_len; `%M.Mkprog_cond?.pc_shape;
              `%Perm.perm_f_to_list; `%Ll.initi; `%Perm.id_n; `%Perm.mk_perm_f];
  delta_qualifier ["unfold"];
  delta_attr [`%SE.__steel_reduce__];
  iota; zeta; primops
]

let __normal_SF : list norm_step = [
  delta_only [`%SF.repr_SF_of_ST_rall; `%SF.repr_SF_of_ST; `%SF.shape_SF_of_ST; `%SF.shape_SF_of_ST_rall;
              `%SF.post_SF_of_ST; `%SF.postl_SF_of_ST; `%SF.post_bij;
              `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
              `%SF.Mkpost_bij_t'?.len_SF; `%SF.Mkpost_bij_t'?.idx_SF; `%SF.Mkpost_bij_t'?.idx_ST;
              `%Ll.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%L.length;
              `%SF.sel_ST_of_SF; `%SF.sell_ST_of_SF; `%SF.post_src_of_shape;
              `%SF.post_src_f_of_shape; `%SF.sel_SF_of_ST; `%SF.sell_SF_of_ST;
              `%Fl.splitAt_ty; `%Fl.head; `%Fl.tail;
              `%Fl.dlist_of_f; `%Dl.initi; `%Fl.cons; `%Fl.nil;
              `%Mktuple2?._1;`%Mktuple2?._2;
              `%Learn.Option.map;
              `%Perm.perm_f_swap; `%Perm.perm_f_transpose; `%Perm.perm_f_of_pair;
              `%Perm.mk_perm_f; `%Perm.id_n; `%Perm.perm_f_of_list];
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
  delta_only [`%M.vprop_of_list; `%M.rmem_sels'; `%Fl.flist_of_d; `%M.rmem_sl_list; `%M.vpl_sels;
              `%Dl.index; `%L.length; `%L.index; `%Fl.flist];
  delta_attr [`%SE.__reduce__];
  iota; zeta;
]


(***** Calling a [M.repr_steel_t] from a Steel program *)

unfold
let norm_vpl (#a : Type) (x : a) = Pervasives.norm __normal_vprop_list x

inline_for_extraction
val call_repr_steel
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t a pre post req ens)
  : SE.Steel a (M.vprop_of_list' pre) (fun x -> M.vprop_of_list' (post x))
      (requires fun h0      -> req (norm_vpl (M.rmem_sels' pre h0)))
      (ensures  fun h0 x h1 -> ens (norm_vpl (M.rmem_sels' pre h0))
                                x
                                (norm_vpl (M.rmem_sels' (post x) h1)))


(***** Extracting a [M.repr_steel_t] from a [M.repr] *)

/// We mention [t] so that it is specified by the goal, but this type is just a synonym for [M.repr_steel_t].
let extract (a : Type) (pre : M.pre_t) (post : M.post_t a) (req : M.req_t pre) (ens : M.ens_t pre a post)
            (t : M.repr a)
  : Type
  = M.repr_steel_t a pre post req ens


[@@ __tac_helper__]
inline_for_extraction
let __solve_by_wp
      (#a : Type) (#t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (#req : M.req_t pre) (#ens : M.ens_t pre a post)
      (c : M.prog_cond t.repr_tree pre post)
      (t_Fun : (sl0 : M.sl_t pre) ->
               GTot (Fun.prog_tree #SF.sl_tys SF.({val_t = a; sel_t = ST.post_ST_of_M post})))
      (t_Fun_eq : squash (t_Fun == (fun sl0 -> prog_M_to_Fun t c sl0)))
      (wp : squash (Fl.forall_flist (M.vprop_list_sels_t pre) (fun sl0 ->
               req sl0 ==>
               Fun.tree_wp (t_Fun sl0) (fun res -> ens sl0 res.val_v res.sel_v))))
      (ext : M.repr_steel_t a pre post req ens)
      (ext_eq : ext == prog_M_to_Fun_extract_wp t c req ens (fun sl0 -> ()))
  : extract a pre post req ens t
  =
    ext

let solve_by_wp () : Tac unit
  =
    let u_c        = fresh_uvar None in
    let u_t_Fun    = fresh_uvar None in
    let u_t_Fun_eq = fresh_uvar None in
    let u_wp       = fresh_uvar None in
    let u_ext      = fresh_uvar None in
    let u_ext_eq   = fresh_uvar None in
    apply_raw (`(__solve_by_wp (`#u_c) (`#u_t_Fun) (`#u_t_Fun_eq) (`#u_wp) (`#u_ext) (`#u_ext_eq)));

    let t = timer_start   "prog_cond " in
    (* c *)
    unshelve u_c;
    norm __normal_M;
    CSl.build_prog_cond ();

    (* t_Fun *)
    unshelve u_t_Fun_eq;
    (* TODO? stage prog_M_to_Fun to avoid duplication *)
    let t = timer_enter t "normal_M  " in
    norm __normal_M;
    let t = timer_enter t "normal_ST " in
    norm __normal_ST;
    let t = timer_enter t "normal_SF " in
    norm __normal_SF;
    let t = timer_enter t "normal_Fun" in
    norm __normal_Fun;
    let t = timer_enter t "misc      " in
    trefl ();

    (* wp *)
    let t = timer_enter t "Fun_wp    " in
    unshelve u_wp;
    norm __normal_M;
    norm __normal_Fun_spec;
    smt ();

    (* ext *)
    // We normalize the resulting Steel program so that it can be extracted
    let t = timer_enter t "extract   " in
    unshelve u_ext_eq;
    norm [delta_qualifier ["inline_for_extraction"];
          iota; zeta; primops];
    trefl ();
    timer_stop t
