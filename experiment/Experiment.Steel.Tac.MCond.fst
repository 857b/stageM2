module Experiment.Steel.Tac.MCond

module U    = Learn.Util
module M    = Experiment.Steel.Repr.M
module L    = FStar.List.Pure
module Ll   = Learn.List
module Fl   = Learn.FList
module Dl   = Learn.DList
module SE   = Steel.Effect
module SU   = Learn.Steel.Util
module Vpl  = Experiment.Steel.VPropList
module Veq  = Experiment.Steel.VEquiv
module Msk  = Learn.List.Mask
module Opt  = Learn.Option
module Perm = Learn.Permutation

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.Interface
open FStar.Calc
open Experiment.Steel.Tac

(*** Building a [Veq.vequiv] *)

/// [vequiv_sol all src trg] represents the building of a [Veq.vequiv trg src].
/// The order of the arguments is reversed since we build an injection ([M.veq_eq]) from [src] to [trg].
/// If [all] is not set, we allow some elements of [trg] to be left unmatched. In that case [src] needs to be
/// completed with [src_add] in order to obtain a [Veq.vequiv].
[@@ __cond_solver__]
noeq
type vequiv_sol : (all : bool) -> (src : Vpl.vprop_list) -> (trg : Vpl.vprop_list) -> Type =
  | VeqAll : (src : Vpl.vprop_list) -> (trg : Vpl.vprop_list) ->
             (veq : Veq.vequiv trg src) ->
             vequiv_sol true src trg
  | VeqPrt : (src : Vpl.vprop_list) -> (unmatched : Vpl.vprop_list) -> (trg : Vpl.vprop_list) ->
             (veq : Veq.vequiv trg L.(src@unmatched)) ->
             vequiv_sol false src trg

[@@ __cond_solver__]
let vequiv_sol_all (#src #trg : Vpl.vprop_list) (e : vequiv_sol true src trg)
  : Veq.vequiv trg src
  = VeqAll?.veq e

[@@ __cond_solver__]
let vequiv_sol_prt (#src #trg : Vpl.vprop_list) (e : vequiv_sol false src trg)
  : Veq.vequiv trg L.(src @ VeqPrt?.unmatched e)
  = VeqPrt?.veq e


[@@ __cond_solver__]
let vequiv_sol_end (all : bool) (vs : Vpl.vprop_list) : vequiv_sol all vs vs
  = if all then VeqAll vs vs (Veq.vequiv_refl vs) else VeqPrt vs [] vs (Veq.vequiv_refl vs)

[@@ __cond_solver__]
let vequiv_sol_end_prt (trg : Vpl.vprop_list) : vequiv_sol false [] trg
  = VeqPrt [] trg trg (Veq.vequiv_refl trg)


[@@ __cond_solver__]
let vequiv_sol_inj
      (all : bool) (src : Vpl.vprop_list) (trg : Vpl.vprop_list)
      (ij : Veq.partial_injection src trg)
      (e' : vequiv_sol all (Msk.filter_mask (Veq.ij_src_mask ij) src)
                           (Msk.filter_mask (Veq.ij_trg_mask ij) trg))
  : vequiv_sol all src trg
  = match e' with
  | VeqAll src' trg' e' -> VeqAll src trg (Veq.vequiv_inj src trg ij e')
  | VeqPrt src' src_add trg' e' ->
           (**) Veq.extend_partial_injection_src ij src_add;
           (**) Veq.extend_partial_injection_trg ij src_add;
           VeqPrt src src_add trg (Veq.vequiv_inj L.(src@src_add) trg
                                     (Veq.extend_partial_injection ij src_add) e')


/// The SMT fallback phase is an injection whose [map_to_eq] condition is added to [veq_req] and solved by SMT.
/// The injection is built from the graph of equalities between the head symbols of the [vprop']. We do not use the
/// [smt_fallback] attribute.

[@@ __cond_solver__]
let vequiv_sol_inj_SMT_fallback
      (all : bool) (src : Vpl.vprop_list) (trg : Vpl.vprop_list)
      (ij : pre_partial_injection src trg)
      (e' : vequiv_sol all (Msk.filter_mask (Veq.ij_src_mask ij) src)
                           (Msk.filter_mask (Veq.ij_trg_mask ij) trg))
  : vequiv_sol all src trg
  = match e' with
  | VeqAll src' trg' e' ->
           VeqAll src trg (Veq.vequiv_with_req (check_map_to_eq src trg ij) (fun rq ->
             Veq.vequiv_inj src trg (checked_pre_partial_injection ij rq) e'))
  | VeqPrt src' src_add trg' e' ->
           VeqPrt src src_add trg (Veq.vequiv_with_req (check_map_to_eq src trg ij) (fun rq ->
             let ij = checked_pre_partial_injection ij rq in
             (**) Veq.extend_partial_injection_src ij src_add;
             (**) Veq.extend_partial_injection_trg ij src_add;
             Veq.vequiv_inj L.(src@src_add) trg (Veq.extend_partial_injection ij src_add) e'))


(**** pointwise equivalence *)

[@@__cond_solver__]
noeq
type vequiv_pointwise : (pre : Vpl.vprop_list) -> (post : Vpl.vprop_list) -> Type =
  | VeqPt_Nil   :  vequiv_pointwise [] []
  | VeqPt_Cons  : (hd : SE.vprop') -> (pre : Vpl.vprop_list) -> (post : Vpl.vprop_list) ->
                   vequiv_pointwise pre post ->
                   vequiv_pointwise (hd :: pre) (hd :: post)
  | VeqPt_Elim  : (hd : SE.vprop') -> (hds : Vpl.vprop_list) ->
                   (e : Veq.vequiv [hd] hds) ->
                  (pre : Vpl.vprop_list) -> (post : Vpl.vprop_list) ->
                   vequiv_pointwise pre post ->
                   vequiv_pointwise (hd :: pre) L.(hds@post)
  | VeqPt_Intro : (hds : Vpl.vprop_list) -> (hd : SE.vprop') ->
                   (e : Veq.vequiv hds [hd]) ->
                  (pre : Vpl.vprop_list) -> (post : Vpl.vprop_list) ->
                   vequiv_pointwise pre post ->
                   vequiv_pointwise L.(hds@pre) (hd :: post)

[@@__cond_solver__]
let rec vequiv_pointwise_M #pre #post (e : vequiv_pointwise pre post)
  : Tot (Veq.vequiv pre post) (decreases e)
  = match e with
  | VeqPt_Nil -> Veq.vequiv_refl []
  | VeqPt_Cons hd pre' post' e ->
      Veq.vequiv_cons hd (vequiv_pointwise_M e)
  | VeqPt_Elim hd hds e0 pre post e1 ->
      (**) assert_norm (L.append [hd] pre == hd :: pre);
      Veq.vequiv_app e0 (vequiv_pointwise_M e1)
  | VeqPt_Intro hds hd e0 pre post e1 ->
      (**) assert_norm (L.append [hd] post == hd :: post);
      Veq.vequiv_app e0 (vequiv_pointwise_M e1)

[@@__cond_solver__]
let vequiv_sol_pointwise_elim #all #pre0 #pre1 #post
      (e0 : vequiv_pointwise pre0 pre1)
      (e1 : vequiv_sol all post pre1)
  : vequiv_sol all post pre0
  = match e1 with
  | VeqAll post' pre1' e1 ->
      VeqAll post' pre0 (Veq.vequiv_trans (vequiv_pointwise_M e0) e1)
  | VeqPrt post' unmatched pre1' e1 ->
      VeqPrt post' unmatched pre0 (Veq.vequiv_trans (vequiv_pointwise_M e0) e1)

[@@__cond_solver__]
let vequiv_sol_pointwise_intro #all #pre #post0 #post1
      (e0 : vequiv_pointwise post0 post1)
      (e1 : vequiv_sol all post0 pre)
  : vequiv_sol all post1 pre
  = match e1 with
  | VeqAll post0' pre' e1 ->
      VeqAll post1 pre' (Veq.vequiv_trans e1 (vequiv_pointwise_M e0))
  | VeqPrt post0' unmatched pre' e1 ->
      VeqPrt post1 unmatched pre
        (Veq.vequiv_trans e1 (Veq.vequiv_app (vequiv_pointwise_M e0) (Veq.vequiv_refl unmatched)))


[@@__cond_solver__]
let veqPt_elim
      (#hd : SE.vprop') (#hds0 #hds1 : Vpl.vprop_list)
      (e0 : Veq.vequiv [hd] hds0) (e1 : vequiv_pointwise hds0 hds1)
      (#pre #post : Vpl.vprop_list)
      (e2 : vequiv_pointwise pre post)
  : vequiv_pointwise (hd :: pre) L.(hds1 @ post)
  = VeqPt_Elim hd hds1 (Veq.vequiv_trans e0 (vequiv_pointwise_M e1)) pre post e2

[@@__cond_solver__]
let veqPt_intro
      (#hds1 #hds0 : Vpl.vprop_list) (#hd : SE.vprop')
      (e0 : Veq.vequiv hds0 [hd]) (e1 : vequiv_pointwise hds1 hds0)
      (#pre #post : Vpl.vprop_list)
      (e2 : vequiv_pointwise pre post)
  : vequiv_pointwise L.(hds1 @ pre) (hd :: post)
  = VeqPt_Intro hds1 hd (Veq.vequiv_trans (vequiv_pointwise_M e1) e0) pre post e2


// TODO: conversion vprop -> vprop_list, pointwise equality
[@@Veq.__vequiv__]
let vequiv_elim_vprop_group (vs : Vpl.vprop_list)
  : Veq.vequiv [SU.vprop_group' (Vpl.vprop_of_list vs)] vs
  = {
    veq_req = (fun _ -> True);
    veq_ens = (fun sl0 sl1 -> Vpl.vpl_sels _ (sl0 0) == Fl.dlist_of_f sl1);
    veq_eq  = L.map (fun _ -> None) vs;
    veq_typ = ();
    veq_g   = (fun opened -> SU.elim_vprop_group (Vpl.vprop_of_list vs))
  }

#push-options "--fuel 2"
[@@Veq.__vequiv__]
let vequiv_intro_vprop_group (vs : Vpl.vprop_list)
  : Veq.vequiv vs [SU.vprop_group' (Vpl.vprop_of_list vs)]
  = {
    veq_req = (fun _ -> True);
    veq_ens = (fun sl0 sl1 -> Vpl.vpl_sels _ (sl1 0) == Fl.dlist_of_f sl0);
    veq_eq  = [None];
    veq_typ = ();
    veq_g   = Steel.Effect.Atomic.(fun opened ->
                 SU.intro_vprop_group (Vpl.vprop_of_list vs);
                 change_equal_slprop (VUnit (SU.vprop_group' (Vpl.vprop_of_list vs)) `star` emp)
                                     (Vpl.vprop_of_list ([SU.vprop_group' (Vpl.vprop_of_list vs)])))
  }
#pop-options


(**** Tac *)

/// If [intro] is set, solves a goal [vequiv_pointwise ?pre post].
/// If [intro] is not set (elim), solves a goal [vequiv_pointwise pre ?post]
/// Returns [true] if an intro/elim has been performed.
#push-options "--ifuel 2"
let rec build_vequiv_pointwise (intro : bool) : Tac bool =
  try apply (`VeqPt_Nil); false with | _ ->
  let b =
    match catch (fun () ->
      if intro
      then begin
        apply (`veqPt_intro);
        // e0
        // currently: only [vprop_group]
        apply (`vequiv_intro_vprop_group)
      end else begin
        apply (`veqPt_elim);
        // e0
        apply (`vequiv_elim_vprop_group)
      end)
    with
    | Inr () -> let _ : bool = build_vequiv_pointwise intro in true
    | Inl _  -> apply (`VeqPt_Cons); false
  in
  let b' = build_vequiv_pointwise intro in
  b || b'
#pop-options

let __normal_vequiv_pointwise : list norm_step = [
    delta_only [`%L.op_At; `%L.append];
    iota; zeta]

exception Cancel

/// On a goal [vequiv_sol all src trg], performs some introductions/eliminations to change the goal into
/// [vequiv_sol all src' trg'].
let rew_vequiv_sol_pointwise () : Tac unit
  =
    begin try
      apply (`vequiv_sol_pointwise_elim);
      if build_vequiv_pointwise false
      then norm __normal_vequiv_pointwise
      // As an optimisation, if not elimination was performed, we do not change the goal's witness
      else raise Cancel
    with Cancel | _ -> ()
    end;
    begin try
      apply (`vequiv_sol_pointwise_intro);
      if build_vequiv_pointwise true
      then norm __normal_vequiv_pointwise
      else raise Cancel
    with Cancel | _ -> ()
    end

let test_vequiv_pointwise_elim (v : int -> SE.vprop')
  : Veq.vequiv [SU.vprop_group' (Vpl.vprop_of_list [v 0; v 1]); v 2] [v 0; v 1; v 2]
  = _ by (
    apply (`Veq.vequiv_trans);
    apply (`vequiv_pointwise_M);
    let b = build_vequiv_pointwise false in
    norm __normal_vequiv_pointwise;
    apply (`Veq.vequiv_refl))

let test_vequiv_pointwise_intro (v : int -> SE.vprop')
  : Veq.vequiv [v 0; v 1; v 2]
             [SU.vprop_group' (Vpl.vprop_of_list [v 0; SU.vprop_group' (Vpl.vprop_of_list [v 1])]); v 2]
  = _ by (
    apply (`Veq.vequiv_trans); flip ();
    apply (`vequiv_pointwise_M);
    let b = build_vequiv_pointwise true in
    norm __normal_vequiv_pointwise;
    apply (`Veq.vequiv_refl))

let test_rew_vequiv_sol_pointwise (v : int -> SE.vprop')
  : vequiv_sol false
      [SU.vprop_group' (Vpl.vprop_of_list [v 0; v 1]); v 2]
      [v 0; SU.vprop_group' (Vpl.vprop_of_list [v 1; v 2])]
  = _ by (
    rew_vequiv_sol_pointwise ();
    apply (`vequiv_sol_end))


let normal_ij_mask : list norm_step = [
  delta_only [`%Msk.filter_mask; `%L.map; `%None?; `%Ll.initi; `%op_Negation; `%L.mem];
  delta_attr [`%__cond_solver__; `%Veq.__vequiv__; `%__tac_helper__];
  delta_qualifier ["unfold"];
  iota; zeta; primops]

let build_vequiv_sol_triv () : Tac unit =
  try apply (`vequiv_sol_end)     with | _ ->
      apply (`vequiv_sol_end_prt)


/// This tactics solves a goal of the form [vequiv_sol all src trg]
let build_vequiv_sol fr ctx (all : bool) : Tac unit
  =
    rew_vequiv_sol_pointwise ();
    try build_vequiv_sol_triv ()
    with | _ ->
      apply_raw (`vequiv_sol_inj);
      build_partial_injection fr ctx;
      norm normal_build_partial_injection;
      norm normal_ij_mask;
    try build_vequiv_sol_triv () with | _ ->
      apply_raw (`vequiv_sol_inj_SMT_fallback);
      build_pre_partial_injection_from_keys fr ctx;
      norm normal_build_partial_injection;
      norm normal_ij_mask;
    try build_vequiv_sol_triv () with | _ ->
      cs_raise fr ctx (fun m -> fail (m Fail_cond_sol []))

(*
let normal_cond_sol_to_equiv : list norm_step = [
    delta_only [`%len; `%L.length; `%L.index; `%L.op_At; `%L.append];
    delta_attr [`%__cond_solver__];
    iota; zeta; primops
  ]

let test_vequiv_sol (v : Char.char -> SE.vprop') :
   (let to_v (s : string) = L.map v (String.list_of_string s) in
    vequiv_sol false (to_v "abca") (to_v "acbdea"))
  = _ by (norm [delta_only [`%L.map]; iota; zeta; primops];
          build_vequiv_sol default_flags dummy_ctx false)    

let _ = assert (U.print_util (fun v -> vequiv_sol_prt (test_vequiv_sol v)))
            by (norm [delta_only [`%test_vequiv_sol]];
                norm normal_build_partial_injection;
                norm normal_cond_sol_to_equiv;
                fail "print")
*)

(*** Building [M.prog_cond] *)

/// The front-end tactic is [build_prog_cond], which solves a goal of the form [M.prog_cond t pre post] where
/// [t], [pre] and [post] are concrete terms (i.e. do not contain uvars).
/// Internally the main work is done by [build_tree_cond] which:
/// - solves a goal of the form [M.prog_cond t pre post] where [t] and [pre] are concrete terms but
///   [post] can be an uvar
/// - returns the shape of the program as a [pre_shape_tree]

let normal_cond_solver : list norm_step = [
    delta_only [`%len; `%None?; `%op_Negation; `%Some?.v;
                `%L.append; `%L.flatten; `%L.hd; `%L.index; `%L.length; `%L.map; `%L.mem; `%L.op_At; `%L.splitAt;
                `%L.tail; `%L.tl;
                `%Ll.initi; `%Ll.set;
                `%Perm.mk_perm_f; `%Perm.perm_f_to_list;
                `%Opt.map; `%Opt.bind;
                `%Fl.forall_flist_part; `%Fl.exists_flist_part;
                `%Fl.partial_app_flist_eq_None; `%Fl.partial_app_flist_eq_Some;
                `%Veq.veq_partial_eq; `%Dl.initi_ty; `%Dl.initi;
                `%Veq.veq_sel_eq_eff; `%Veq.veq_sel_eq_eff_aux;
                `%Vpl.vprop_list_sels_t];
    delta_attr [`%__tac_helper__; `%__cond_solver__; `%Msk.__mask__; `%Veq.__vequiv__];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

let norm_cond_sol () : Tac unit =
  norm normal_cond_solver

[@@ __tac_helper__]
let __defer_post_unification
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post0 : M.post_t a)
      (post1 : M.post_t a)
      (cd : M.tree_cond t pre post1)
      (_ : squash (post0 == post1))
  : M.tree_cond t pre post0
  = cd


/// While building the [M.tree_cond], we also want to build the associated [M.shape_tree].
/// This is done by extracting a [pre_shape_tree]. At the end, [build_prog_cond] quotes the [pre_shape_tree],
/// converts it to a [M.shape_tree] (by using an effective test, [shape_tree_of_pre]) and check that it matches
/// the built [M.tree_cond] (again with an effective test, [M.tree_cond_has_shape]).

let tc_extract_nat () : Tac nat =
  norm_cond_sol ();
  extract_nat_tac ()

[@@ __tac_helper__]
private
let __extract_veq_eq (#pre_n : nat) (l : list (option (Fin.fin pre_n))) : Type
  = extract_term #(list (option int)) (L.map (Opt.map (fun (i : Fin.fin pre_n) -> i <: int)) l)

[@@ __tac_helper__]
private
let __extract_vequiv (#pre #post : Vpl.vprop_list) (e : Veq.vequiv pre post) : Type
  = __extract_veq_eq e.veq_eq

let tc_extract_veq_eq () : Tac (list (option int)) =
  norm_cond_sol ();
  extract_term_tac (unquote #(list (option int)))

type pre_shape_tree : (pre_n : int) -> (post_n : int) -> Type =
  | PSspec  : (pre_n : int) -> (post_n : int) -> (pre'_n : int) -> (post'_n : int) -> (frame_n : int) ->
              (e_pre : list (option int)) -> (e_post : list (option int)) ->
              pre_shape_tree pre'_n post'_n
  | PSret   : (pre_n : int) -> (post_n : int) -> (e : list (option int)) ->
              pre_shape_tree pre_n post_n
  | PSbind  : (pre_n : int) -> (itm_n : int) -> (post_n : int) ->
              (f : pre_shape_tree pre_n itm_n) -> (g : pre_shape_tree itm_n post_n) ->
              pre_shape_tree pre_n post_n
  | PSbindP : (pre_n : int) -> (post_n : int) ->
              (g : pre_shape_tree pre_n post_n) ->
              pre_shape_tree pre_n post_n
  | PSif    : (pre_n : int) -> (post_n : int) ->
              (thn : pre_shape_tree pre_n post_n) ->
              (els : pre_shape_tree pre_n post_n) ->
              pre_shape_tree pre_n post_n

type shape_tree_t = (pre_n : nat & post_n : nat & pre_shape_tree pre_n post_n)

let rec veq_eq_list_checked_aux (pre_n : nat) (l : list (option int))
  : Tot (option (list (option (Fin.fin pre_n)))) (decreases l)
  = match l with
  | [] -> Some []
  | Some x :: xs -> if 0 <= x && x < pre_n
                  then Opt.map (Cons (Some (x <: Fin.fin pre_n))) (veq_eq_list_checked_aux pre_n xs)
                  else None
  | None   :: xs -> Opt.map (Cons None) (veq_eq_list_checked_aux pre_n xs)

let veq_eq_list_checked (pre_n : nat) (post_n : nat) (l : list (option int))
  : option (Veq.veq_eq_t_list pre_n post_n) =
  match veq_eq_list_checked_aux pre_n l with
  | Some r -> if L.length r = post_n then Some r else None
  | None   -> None
  

let rec shape_tree_of_pre (#pre_n : nat) (#post_n : nat) (ps : pre_shape_tree pre_n post_n)
  : Tot (option (M.shape_tree pre_n post_n)) (decreases ps)
  = match ps with
  | PSspec pre_n post_n pre'_n post'_n frame_n e_pre e_post ->
           if pre_n >= 0 && post_n >= 0 && frame_n >= 0
           then match veq_eq_list_checked pre'_n (pre_n + frame_n) e_pre,
                      veq_eq_list_checked (post_n + frame_n) post'_n e_post
           with
           | Some e0, Some e1 -> Some (M.Sspec pre_n post_n pre'_n post'_n frame_n e0 e1)
           | _ -> None
           else None
  | PSret pre_n post_n e ->
          (match veq_eq_list_checked pre_n post_n e with
          | Some e -> Some (M.Sret pre_n post_n e)
          | _ -> None)
  | PSbind pre_n itm_n post_n f g ->
          if itm_n >= 0
          then match shape_tree_of_pre f, shape_tree_of_pre g with
          | Some f, Some g -> Some (M.Sbind pre_n itm_n post_n f g)
          | _ -> None
          else None
  | PSbindP pre_n post_n g ->
          (match shape_tree_of_pre g with
          | Some g -> Some (M.SbindP pre_n post_n g)
          | _ -> None)
  | PSif pre_n post_n thn els ->
          (match shape_tree_of_pre thn, shape_tree_of_pre els with
          | Some thn, Some els -> Some (M.Sif pre_n post_n thn els)
          | _ -> None)


/// The following tactics solve goals of the form [M.tree_cond t pre t_post] where [t_post] is a concrete term if
/// the boolean parameter [post] is set and an uvar otherwise.
/// The resolution is done by solving some [cond_sol] problems. By branching on the [post] parameter, one can
/// ensure that those problems are fully instantiated. That is we use different building functions depending on
/// whether the post-condition is known ('_p' (post) functions like [__build_TCspec_p]) or has to be
/// inferred ('_u' (uvar) functions like [__build_TCspec_u]).

[@@ __tac_helper__]
let __build_TCspec_u
      (#a : Type) (#sp : M.spec_r a -> Type)
      (#s : M.spec_r a) (sh : sp s)
      (#pre' : M.pre_t)
      (cs0 : vequiv_sol false s.spc_pre pre')

      (pre_n   : extract_term (L.length s.spc_pre))
      (post_n  : (x : a) -> extract_term (L.length (s.spc_post x)))
      (pre'_n  : extract_term (L.length pre'))
      (post'_n : (x : a) -> extract_term L.(length (s.spc_post x @ VeqPrt?.unmatched cs0)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))

  : M.tree_cond (M.Tspec a sp) pre' (fun (x : a) -> L.(s.spc_post x @ VeqPrt?.unmatched cs0))
  =
    let frame = VeqPrt?.unmatched cs0 in
    M.TCspec s sh M.({
      tcs_pre     = pre';
      tcs_post    = (fun x -> L.(s.spc_post x @ frame));
      tcs_frame   = frame;
      tcs_pre_eq  = vequiv_sol_prt cs0;
      tcs_post_eq = (fun x -> Veq.vequiv_refl L.(s.spc_post x @ frame))
    })

[@@ __tac_helper__]
let __build_TCspec_p
      (#a : Type) (#sp : M.spec_r a -> Type)
      (#s : M.spec_r a) (sh : sp s)
      (#pre' : M.pre_t) (#post' : M.post_t a)
      (cs0 : vequiv_sol false s.spc_pre pre')
      (cs1 : (x : a) -> vequiv_sol true (post' x) L.(s.spc_post x @ VeqPrt?.unmatched cs0))

      (pre_n   : extract_term (L.length s.spc_pre))
      (post_n  : (x : a) -> extract_term (L.length (s.spc_post x)))
      (pre'_n  : extract_term (L.length pre'))
      (post'_n : (x : a) -> extract_term L.(length (post' x)))
      (frame_n : extract_term (L.length (VeqPrt?.unmatched cs0)))
      (p0 : __extract_vequiv (vequiv_sol_prt cs0))
      (p1 : (x : a) -> __extract_vequiv (vequiv_sol_all (cs1 x)))

  : M.tree_cond (M.Tspec a sp) pre' post'
  =
    M.TCspec s sh M.({
      tcs_pre     = pre';
      tcs_post    = post';
      tcs_frame   = VeqPrt?.unmatched cs0;
      tcs_pre_eq  = vequiv_sol_prt cs0;
      tcs_post_eq = (fun x -> vequiv_sol_all (cs1 x))
    })


/// By default, if the post-condition of a [M.Tret] has to be inferred, we simply choose [fun _ -> pre]. That is,
/// we do not introduce any dependency in the returned value.
/// It is possible to modify this behaviour by annotating the [M.Tret] with [sl_hint : M.post_t a], which
/// specifies some vprops that should depend on the returned value (it does not need to mention the vprops that
/// do not depend on the returned value).
/// The default behaviour is obtained with [sl_hint = fun _ -> []].
/// This hint is ignored if the post-condition is known from the context ([__build_TCret_p]).
/// See [test_build_tree_cond__Tret_u_0] for a minimal example where it is needed.
[@@ __tac_helper__]
let __build_TCret_u
      (#a : Type) (#x : a) (#sl_hint : M.post_t a)
      (#pre : M.pre_t)
      (cs : vequiv_sol false (sl_hint x) pre)
      
      (pre_n  : extract_term (L.length pre))
      (post_n : (x : a) -> extract_term L.(length (sl_hint x @ VeqPrt?.unmatched cs)))
      (p : __extract_vequiv (vequiv_sol_prt cs))

  : M.tree_cond (M.Tret a x sl_hint) pre (fun x -> L.(sl_hint x @ VeqPrt?.unmatched cs))
  =
    M.TCret pre (fun x -> L.(sl_hint x @ VeqPrt?.unmatched cs)) (vequiv_sol_prt cs)

[@@ __tac_helper__]
let __build_TCret_p
      (#a : Type) (#x : a) (#sl_hint : M.post_t a)
      (#pre : M.pre_t) (#post : M.post_t a)
      (cs : vequiv_sol true (post x) pre)

      (pre_n  : extract_term (L.length pre))
      (post_n : (x : a) -> extract_term L.(length (post x)))
      (p : __extract_vequiv (vequiv_sol_all cs))

  : M.tree_cond (M.Tret a x sl_hint) pre post
  =
    M.TCret #a #x pre post (vequiv_sol_all cs)


let build_TCspec fr (post : bool) : Tac shape_tree_t
  =
    if post then begin
      apply_raw (`__build_TCspec_p);
      // s
      dismiss ();
      // sh
      build_spec_r fr (fun () -> [Info_location "in the spec statement"]);
      // cs0
      norm_cond_sol ();
      build_vequiv_sol fr (fun () -> [Info_location "before the spec statement"]) false;
      // cs1
      norm_cond_sol ();
      let x = intro () in
      build_vequiv_sol fr (fun () -> [Info_location "after the spec statement"]) true
    end else begin
      apply_raw (`__build_TCspec_u);
      // s
      dismiss ();
      // sh
      build_spec_r fr (fun () -> [Info_location "in the spec statement"]);
      // cs0
      norm_cond_sol ();
      build_vequiv_sol fr (fun () -> [Info_location "before the spec statement"]) false
    end;

    let pre_n   = tc_extract_nat ()                     in
    let post_n  = let _ = intro () in tc_extract_nat () in
    let pre'_n  = tc_extract_nat ()                     in
    let post'_n = let _ = intro () in tc_extract_nat () in
    let frame_n = tc_extract_nat ()                     in
    let e_pre = tc_extract_veq_eq ()                    in
    let e_post : list (option int) =
      if post then let _ = intro () in tc_extract_veq_eq ()
      else Ll.initi 0 post'_n (fun i -> Some (i <: int))
    in
    (|pre'_n, post'_n, PSspec pre_n post_n pre'_n post'_n frame_n e_pre e_post|)

let build_TCret fr (post : bool) : Tac shape_tree_t
  = if post then begin
      apply_raw (`__build_TCret_p);
      build_vequiv_sol fr (fun () -> [Info_location "after the return statement"]) true
    end else begin
      let cs = fresh_uvar None in
      apply_raw (`(__build_TCret_u (`#cs)));
      unshelve cs;
      build_vequiv_sol fr (fun () -> [Info_location "after the return statement"]) false
    end;

    let pre_n  = tc_extract_nat ()                     in
    let post_n = let _ = intro () in tc_extract_nat () in
    let e      = tc_extract_veq_eq ()                  in
    (|pre_n, post_n, PSret pre_n post_n e|)

let rec build_TCbind fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCbind);
    let (|pre_f, post_f, s_f|) = build_tree_cond fr false in
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond fr post  in

    if post_f <> pre_g then cs_raise fr (fun () -> [Info_location "in the bind statement"])
                                    (fun m -> fail (m (Fail_shape_unification post_f pre_g) []));
    (|pre_f, post_g, PSbind pre_f post_f post_g s_f s_g|)

and build_TCbindP fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCbindP);
    let x = intro () in
    let (|pre_g, post_g, s_g|) = build_tree_cond fr post in
    (|pre_g, post_g, PSbindP pre_g post_g s_g|)

/// If the post-condition of an `if` statement is not specified, it is inferred from the `then` branch.
/// Any annotation ([sl_hint] for the return) for the post-condition of the `if` should thus be on the first branch.
and build_TCif fr (post : bool) : Tac shape_tree_t
  = apply (`M.TCif);
    let (|pre_thn, post_thn, s_thn|) = build_tree_cond fr post in
    let (|pre_els, post_els, s_els|) = build_tree_cond fr true in

    let ctx () = [Info_location "in the if statement"] in
    if pre_thn  <> pre_els  then cs_raise fr ctx (fun m -> fail (m (Fail_shape_unification pre_thn pre_els) []));
    if post_thn <> post_els then cs_raise fr ctx (fun m -> fail (m (Fail_shape_unification post_thn post_els) []));
    (|pre_thn, post_thn, PSif pre_thn post_thn s_thn s_els|)

and build_tree_cond fr (post : bool) : Tac shape_tree_t
  =
    let build_tac : flags_record -> bool -> Tac shape_tree_t =
      let goal = cur_goal () in
      let args = (collect_app goal)._2 in
      let fail_shape () =
        cs_raise fr dummy_ctx (fun m -> fail (m (Fail_goal_shape GShape_tree_cond) [Info_goal goal])) in
      if L.length args <> 4
      then fail_shape ()
      else let hd = (collect_app (L.index args 1)._1)._1 in
      match inspect hd with
      | Tv_FVar fv | Tv_UInst fv _ ->
          let nd = inspect_fv fv in
          match_M_prog_tree fr dummy_ctx nd
            build_TCspec build_TCret build_TCbind build_TCbindP build_TCif
      | r -> fail_shape ()
    in
    if post
    then build_tac fr true
    else begin
      // If post is false, the post is an uvar [post0] that may be independent of some bound variables the current
      // [M.prog_tree] and pre can depend on.
      // If we try to build directly a [tree_cond_sol] for [post0], the unification can fail since we need
      // to normalize the inferred post in order to see the variables it depends on.
      // Hence we introduce a fresh uvar [post1] for the inferred post. [post1] can depend on all the variables
      // in scope but should (in a correct program) only depends on the variables in scope for [post0].
      // We then normalize [post1] and try to assign the result to [post0].
      let post1 = fresh_uvar None in
      // Changes the goal [tree_cond_sol t pre ?post0] into [tree_cond_sol t pre ?post1] and [?post0 == ?post1]
      apply_raw (`(__defer_post_unification (`#post1)));
      // Solves [tree_cond_sol t pre post1]
      let shp = build_tac fr false in
      // [?post1] is now inferred as [post1] and we are presented with a goal [?post0 == post1].
      // We normalize [post1] and assign the result to [?post0].
      norm_cond_sol ();
      cs_try trefl fr dummy_ctx (fun m -> fail (m Fail_post_unification []));

      shp
    end


[@@ __tac_helper__]
private inline_for_extraction
let __build_prog_cond
      (#a : Type) (#t : M.prog_tree a) (#pre : M.pre_t) (#post : M.post_t a)
      (tc0 : M.tree_cond t pre post)
      (#tc : M.tree_cond t pre post) (_ : squash (tc == tc0)) // allows to normalize tc
      (#pre_n : int) (#post_n : int) (ps : pre_shape_tree pre_n post_n)
      (_ : squash (pre_n >= 0 /\ post_n >= 0 /\ pre_n == len pre))
      (#s : M.shape_tree pre_n post_n) (_ : squash (Some s == shape_tree_of_pre ps))
      (_ : M.tree_cond_has_shape tc s)
  : M.prog_cond t pre post
  = M.({ pc_tree     = tc;
         pc_post_len = post_n;
         pc_shape    = s })

let intro_l_True : l_True = ()
let intro_squash_l_True : squash (l_True) = ()

/// This is the front-end tactics. It solves a goal of the form [M.prog_cond t pre post].
let build_prog_cond fr : Tac unit
  =
    let tc0   = fresh_uvar None in
    let tc_eq = fresh_uvar None in
    let ushp  = fresh_uvar None in
    apply (`(__build_prog_cond (`#tc0) (`#tc_eq) (`#ushp)));
    // [M.tree_cond t pre post]
    unshelve tc0;
    let (|pre_n, post_n, shp|) = build_tree_cond fr true in
    // tc <- tc0
    unshelve tc_eq;
    norm_cond_sol ();
    norm [simplify];
    trefl ();
    // shp
    unshelve ushp;
    exact (quote shp);
    // some checks
    norm [delta_only [`%L.length; `%len]; iota; zeta; primops; simplify];
    exact (`intro_squash_l_True);
    // [shape_tree_of_pre]
    norm [delta_only [`%shape_tree_of_pre;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi; `%L.index; `%L.list_ref; `%Ll.set
                     ];
          iota; zeta; primops];
    trefl ();
    // [M.tree_cond_has_shape tc shp]
    norm [delta_only [`%M.tree_cond_has_shape; `%Perm.perm_f_to_list; `%Perm.mk_perm_f; `%Perm.mk_perm_f;
                      `%Perm.perm_f_eq; `%Perm.perm_f_of_list; `%Perm.id_n;
                      `%L.length; `%L.hd; `%L.tl; `%L.tail; `%L.index; `%L.op_At; `%L.append;
                      `%Ll.initi; `%Ll.list_eq;
                      `%Opt.opt_eq;
                      `%U.cast];
          delta_qualifier ["unfold"];
          delta_attr [`%__tac_helper__; `%Veq.__vequiv__];
          iota; zeta; primops; simplify];
    exact (`intro_l_True)
