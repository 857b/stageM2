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

(*// TODO: conversion vprop -> vprop_list, pointwise equality
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
*)

(**** Tac *)

/// If [intro] is set, solves a goal [vequiv_pointwise ?pre post].
/// If [intro] is not set (elim), solves a goal [vequiv_pointwise pre ?post]
/// Returns [true] if an intro/elim has been performed.
#push-options "--ifuel 2"
let (*rec*) build_vequiv_pointwise (intro : bool) : Tac bool =
  (*try apply (`VeqPt_Nil); false with | _ ->
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
  b || b'*)
  false
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

(*
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
*)


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
