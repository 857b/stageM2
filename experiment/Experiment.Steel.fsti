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
  : (sl0 : M.sl_f pre) ->
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
    begin fun (sl0 : M.sl_f pre) ->
      let t_SF = SF.repr_SF_of_ST_rall t_ST' s_ST' sl0 in
      SF.repr_Fun_of_SF t_SF
    end

val prog_M_to_Fun_equiv
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (sl0 : M.sl_f pre)
  : Lemma (M.tree_req t.repr_tree c.pc_tree sl0 <==> Fun.tree_req (prog_M_to_Fun t c sl0) /\
          (M.tree_req t.repr_tree c.pc_tree sl0 ==>
          (forall (x : a) (sl1 : M.sl_f (post x)) .
               (M.tree_ens t.repr_tree c.pc_tree sl0 x sl1 <==>
                Fun.tree_ens (prog_M_to_Fun t c sl0) SF.({val_v = x; sel_v = sl1})))))

inline_for_extraction
let prog_M_to_Fun_extract
      (#a : Type) (t : M.repr a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (c : M.prog_cond t.repr_tree pre post)
      (req : M.req_t pre) (ens : M.ens_t pre a post)
      (sub : (sl0 : M.sl_f pre) -> Lemma (requires req sl0)
               (ensures Fun.tree_req (prog_M_to_Fun t c sl0) /\
                  (forall (x : a) (sl1 : M.sl_f (post x)) .
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
      (wp : (sl0 : M.sl_f pre) -> Lemma
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
  delta_only [`%M.vprop_of_list; `%M.vprop_list_sels_t; `%M.sel_f'; `%M.sel';
              `%Fl.flist_of_g; `%Fl.dlist_of_f_g; `%Fl.flist_of_d;
              `%Dl.index; `%Dl.initi_g;
              `%L.length; `%L.index; `%L.map; `%L.hd; `%L.tl; `%L.tail];
  delta_attr [`%SE.__reduce__];
  iota; zeta; primops
]

/// Steps for normalizing [M.flatten_vprop v].
let __normal_flatten_vprop : list norm_step = [
  delta_only [`%M.flatten_vprop; `%M.flatten_vprop_aux];
  delta_attr [`%SE.__reduce__];
  delta_qualifier ["unfold"];
  iota; zeta; primops
]

/// Steps for the normalisation of Steel's requires and ensures clauses.
/// We need [__steel_reduce__] in order to unfold the selector functions
/// (for instance [Steel.Reference.sel])
let __normal_Steel_logical_spec : list norm_step = [
  delta_only [`%SE.VUnit?._0];
  delta_attr [`%SE.__reduce__; `%SE.__steel_reduce__];
  delta_qualifier ["unfold"];
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
      (r : M.repr_steel_t a pre post req ens)
  : SE.Steel a (M.vprop_of_list' pre) (fun x -> M.vprop_of_list' (post x))
      (requires fun h0      -> norm_vpl (req (M.sel_f' pre h0)))
      (ensures  fun h0 x h1 -> norm_vpl (ens (M.sel_f' pre h0) x (M.sel_f' (post x) h1)))


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
      (t_Fun : (sl0 : M.sl_f pre) ->
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

/// Solves a goal of the form [extract a pre post req ens t]
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


(***** Extracting a [M.unit_steel] from a [M.repr] *)

(*// This fail, seemingly because of the expansion of the memories when checking the post
[@@ handle_smt_goals ]
let tac () = dump "SMT query"
let steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (f : M.unit_steel a pre post req ens)
  : SE.Steel a pre post req ens
  = f ()*)

[@@ __tac_helper__]
noeq
type to_repr_t (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
= {
  r_pre  : M.pre_t;
  r_post : M.post_t a;
  r_req  : M.req_t r_pre;
  r_ens  : M.ens_t r_pre a r_post;
  r_pre_eq  : unit -> Lemma (pre `SE.equiv` M.vprop_of_list r_pre);
  r_post_eq : (x : a) -> Lemma (post x `SE.equiv` M.vprop_of_list (r_post x));
  r_req_eq  : (h0 : SE.rmem pre) -> Lemma (req h0 ==
                  r_req (M.sel r_pre (
                          r_pre_eq ();
                          SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                          SE.focus_rmem h0 (M.vprop_of_list r_pre))));
  r_ens_eq  : (h0 : SE.rmem pre) -> (x : a) -> (h1 : SE.rmem (post x)) -> Lemma (ens h0 x h1 ==
                  r_ens (M.sel r_pre (
                          r_pre_eq ();
                          SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                          SE.focus_rmem h0 (M.vprop_of_list r_pre)))
                        x
                        (M.sel (r_post x) (
                          r_post_eq x;
                          SE.equiv_can_be_split (post x) (M.vprop_of_list (r_post x));
                          SE.focus_rmem h1 (M.vprop_of_list (r_post x)))))
}

inline_for_extraction
val steel_of_repr
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (tr : to_repr_t a pre post req ens)
      (f : M.repr_steel_t a tr.r_pre tr.r_post tr.r_req tr.r_ens)
  : M.unit_steel a pre post req ens

val __build_to_repr_t_lem
      (p : SE.vprop) (r_p : M.vprop_list {p `SE.equiv` M.vprop_of_list r_p}) (h : SE.rmem p)
      (v : SE.vprop{SE.can_be_split p v}) (_ : squash (SE.VUnit? v))
      (i : CSl.elem_index (SE.VUnit?._0 v) r_p)
      (i' : int) (_ : squash (i' == i))
  : squash (h v ==
        M.sel r_p (SE.equiv_can_be_split p (M.vprop_of_list r_p);
                   SE.focus_rmem h (M.vprop_of_list r_p)) i)

[@@ __tac_helper__]
let __build_to_repr_t
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)

      (e_pre  : M.vprop_with_emp pre) (r_pre  : M.pre_t)
      (pre_eq  : squash (r_pre == M.flatten_vprop e_pre))

      (e_post : (x : a) -> M.vprop_with_emp (post x)) (r_post : M.post_t a)
      (post_eq : (x : a) -> squash (r_post x == M.flatten_vprop (e_post x)))

      (#r_req  : M.req_t r_pre)
      (r_req_eq  : (h0 : SE.rmem pre) -> (sl0 : M.sl_f r_pre) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : CSl.elem_index (SE.VUnit?._0 v) r_pre) ->
                             // This indirection is needed so that [apply_raw] presents a goal for [i]
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                    r_req sl0 == req h0)

      (#r_ens  : M.ens_t r_pre a r_post)
      (r_ens_eq  : (h0 : SE.rmem pre) -> (sl0 : M.sl_f r_pre) ->
                   (x : a) ->
                   (h1 : SE.rmem (post x)) -> (sl1 : M.sl_f (r_post x)) ->
                   (sl0_eq : ((v : SE.vprop{SE.can_be_split pre v}) -> squash (SE.VUnit? v) ->
                             (i : CSl.elem_index (SE.VUnit?._0 v) r_pre) ->
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h0 v == sl0 i'))) ->
                   (sl1_eq : ((v : SE.vprop{SE.can_be_split (post x) v}) -> squash (SE.VUnit? v) ->
                             (i : CSl.elem_index (SE.VUnit?._0 v) (r_post x)) ->
                             (i' : int) -> (_ : squash (i' == i)) ->
                             squash (h1 v == sl1 i'))) ->
                   r_ens sl0 x sl1 == ens h0 x h1)

  : to_repr_t a pre post req ens
  = 
    let r_pre_eq () : Lemma (pre `SE.equiv` M.vprop_of_list r_pre)
      = pre_eq;
        M.vprop_equiv_flat pre e_pre;
        SE.equiv_sym (M.vprop_of_list r_pre) pre                in
    let r_post_eq (x : a) : Lemma (post x `SE.equiv` M.vprop_of_list (r_post x))
      = post_eq x;
        M.vprop_equiv_flat (post x) (e_post x);
        SE.equiv_sym (M.vprop_of_list (r_post x)) (post x)
    in
    {
    r_pre; r_post; r_req; r_ens;
    r_pre_eq; r_post_eq;
    r_req_eq  = (fun (h0 : SE.rmem pre) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (M.vprop_of_list r_pre) in
                   r_req_eq h0 (M.sel r_pre h0_r)
                            (__build_to_repr_t_lem pre r_pre h0));
    r_ens_eq  = (fun (h0 : SE.rmem pre) (x : a) (h1 : SE.rmem (post x)) ->
                   r_pre_eq ();
                   SE.equiv_can_be_split pre (M.vprop_of_list r_pre);
                   let h0_r = SE.focus_rmem h0 (M.vprop_of_list r_pre) in
                   r_post_eq x;
                   SE.equiv_can_be_split (post x) (M.vprop_of_list (r_post x));
                   let h1_r = SE.focus_rmem h1 (M.vprop_of_list (r_post x)) in
                   r_ens_eq h0 (M.sel r_pre h0_r) x h1 (M.sel (r_post x) h1_r)
                            (__build_to_repr_t_lem pre r_pre h0)
                            (__build_to_repr_t_lem (post x) (r_post x) h1))
  }

(**) private val __begin_tacs : unit

let filter_rmem_apply (#p : SE.vprop) (h : SE.rmem p) (v : SE.vprop{SE.can_be_split p v})
  #sl (_ : squash (h v == sl))
  : squash (h v == sl)
  = ()

/// Given a term [squash (lhs == rhs)], this tactics returns [Some (h, v)] if [lhs] is [h v]
/// UNUSED: using v generates a SMT goal [SE.can_be_split]
let match_rmem_apply (t : term) : Tac (option (term & term))
  = match inspect t with
    | Tv_App _squash (eq, Q_Explicit) ->
      let _, ts = collect_app eq in
      let n_args = L.length ts in
      if n_args <> 3 then fail ("unexpected shape1:"^string_of_int n_args)
      else let lhs = (L.index ts 1)._1 in
     (match inspect lhs with
      | Tv_App h (v, Q_Explicit) -> Some (h, v)
      | _ -> None)
    | _ -> fail "unexpected shape0"

/// Solves a goal [to_repr_t a pre post req ens]
let build_to_repr_t () : Tac unit
  =
    let u_r_pre  = fresh_uvar None in
    let u_r_post = fresh_uvar None in
    let u_r_req  = fresh_uvar None in
    let u_r_ens  = fresh_uvar None in
    apply_raw (`__build_to_repr_t);

    (* [r_pre] *)
    CSl.build_vprop_with_emp ();
    exact u_r_pre;
    norm __normal_flatten_vprop;
    trefl ();

    (* [r_post] *)
    let _ = intro () in
      CSl.build_vprop_with_emp ();
    exact u_r_post;
    let _ = intro () in
      norm __normal_flatten_vprop;
      trefl ();

    // apply the rewriting hypothesis [eq_lem] to solve a goal [squash (h v == sl ?i)]
    let apply_rew eq_lem =
      apply_raw eq_lem;
      // [VUnit?]
      norm [delta_only [`%SE.VUnit?]; iota];
      trivial ();
      // [elem_index]
      norm __normal_Steel_logical_spec;
      CSl.build_elem_index ();
      // [i' <- i]
      norm [delta_attr [`%CSl.__cond_solver__; `%__tac_helper__]];
      trefl ()
    in

    (* [r_req] *)
    exact u_r_req;
    let h0 = intro () in let sl0 = intro () in let eq0 = intro () in
      // This normalisation has to be done after introducing [eq0], otherwise its application fails,
      // seemingly because of the normalisation of [t_of].
      norm __normal_Steel_logical_spec;
      pointwise begin fun () ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#h0))) with
        | Inr () -> // For some reason, this can only be applied on the goal produced by [filter_rmem_apply]
                   apply_rew eq0
        | Inl _  -> trefl ()
      end;
      trefl ();

    (* [r_ens] *)
    exact u_r_ens;
    let h0  = intro () in let sl0 = intro () in
    let x   = intro () in
    let h1  = intro () in let sl1 = intro () in
    let eq0 = intro () in let eq1 = intro () in
      norm __normal_Steel_logical_spec;
      pointwise begin fun () ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#h0))) with
        | Inr () -> apply_rew eq0
        | Inl _ ->
        match catch (fun () -> apply_raw (`filter_rmem_apply (`#h1))) with
        | Inr () -> apply_rew eq1
        | Inl _  -> trefl ()
      end;
      trefl ()


/// Similarly to [extract], [t] is only mentioned so that it can be retrieved by the tactic
type __to_steel_goal
      (a : Type) (pre : SE.pre_t) (post : SE.post_t a) (req : SE.req_t pre) (ens : SE.ens_t pre a post)
      (t : M.repr a)
  = M.unit_steel a pre post req ens

[@@ __tac_helper__]
inline_for_extraction
let __build_to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (#t : M.repr a)
      (goal_tr : to_repr_t a pre post req ens)
      (goal_f  : extract a goal_tr.r_pre goal_tr.r_post goal_tr.r_req goal_tr.r_ens t)
  : __to_steel_goal a pre post req ens t
  = steel_of_repr goal_tr goal_f

/// Solves a goal [__to_steel_goal]
// FIXME: this tactic get stuck if this file is lax-checked
let build_to_steel () : Tac unit
  =
    // This tactics fails if called in lax mode.
    // It appears that at this point the goal contains unification variables in lax-mode:
    //   __to_steel_goal unit ?pre ?post ?req ?ens t
    // whereas the specifications are concrete terms (inferred from the top-level annotation) in normal-mode.
    // If we try to solve the goal with [lax_guard], Steel then fails to solve some [equiv] with the
    // [__lax_made] introduced for the specifications.
    let t = timer_start "specs     " in
    apply_raw (`__build_to_steel);
    build_to_repr_t ();
    timer_stop t;

    // [extract]
    norm [delta_attr [`%__tac_helper__]; iota];
    solve_by_wp ()


[@@ __tac_helper__]
inline_for_extraction
let to_steel
      (#a : Type) (#pre : SE.pre_t) (#post : SE.post_t a) (#req : SE.req_t pre) (#ens : SE.ens_t pre a post)
      (t : M.repr a)
      (g : __to_steel_goal a pre post req ens t)
  : M.unit_steel a pre post req ens
  = g

(**) private val __end_tacs : unit
