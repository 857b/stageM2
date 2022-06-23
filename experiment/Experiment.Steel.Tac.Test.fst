module Experiment.Steel.Tac.Test

module M    = Experiment.Steel.Repr.M
module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module LV   = Experiment.Steel.Repr.LV
module Fin  = FStar.Fin
module Perm = Learn.Permutation

open FStar.Tactics
open Learn.Tactics.Util
open Experiment.Steel.VPropList
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open Experiment.Steel.Interface
open Experiment.Steel.Tac


let test_flags = make_flags_record [Full_Msg]

let _ : elem_index #int 4 [1;3;4;2;7]
  = _ by (build_elem_index test_flags dummy_ctx)

#push-options "--silent"

[@@ expect_failure [228]]
let _ : elem_index #int 5 [1;3;4;2;7]
  = _ by (build_elem_index test_flags dummy_ctx)

[@@ expect_failure [228]]
let _ : elem_index #int 4 L.(0 :: ([1;3] @ [4;2;7]))
  = _ by (build_elem_index test_flags dummy_ctx)

#pop-options


let test_build_to_repr_t_0 (r r' : ref nat)
  : M.to_repr_t int (vptr r) (fun x -> vptr r') (fun h0 -> sel r h0 < 10) (fun h0 x h1 -> sel r h0 + x < sel r' h1)
  = _ by (build_to_repr_t default_flags dummy_ctx)

#push-options "--silent"

[@@ expect_failure [228]]
let test_build_to_repr_t_1 (r : ref nat) (p : (a : Type) -> (x : a) -> prop)
  : M.to_repr_t int (vptr r) (fun x -> emp) (fun h0 -> p _ h0) (fun h0 x h1 -> True)
  = _ by (build_to_repr_t default_flags dummy_ctx)

[@@ expect_failure [228]]
let test_build_to_repr_t_2 (r r' : ref nat)
  : M.to_repr_t int (vptr r `star` vptr r') (fun x -> emp) (fun h0 -> (h0 (vptr r `star` vptr r'))._1 <= 10) (fun h0 x h1 -> True)
  = _ by (build_to_repr_t default_flags dummy_ctx)

#pop-options


unfold
let specT (a : Type) (pre : M.pre_t) (post : M.post_t a) : M.prog_tree a
  = M.Tspec a (M.spec_r_exact (M.Mkspec_r pre post (fun _ -> True) (fun _ _ _ -> True)))

let rec repeat_n (n : nat) (t : M.prog_tree unit) : M.prog_tree unit
  = if n = 0 then M.Tret unit () (fun _ -> [])
    else M.Tbind unit unit t (fun () -> repeat_n (n-1) t)

let norm_test () : Tac unit
  = norm [delta_only [`%repeat_n; `%Ll.initi];
          delta_qualifier ["unfold"];
          iota; zeta; primops]


(*** LV *)

open Experiment.Steel.Tac.LV

noeq
type lin_cond_r (env : vprop_list) (#a : Type) (t : M.prog_tree a) = {
  lcr_csm : LV.csm_t env;
  lcr_prd : LV.prd_t a;
  lcr_lc  : LV.lin_cond env t lcr_csm lcr_prd
}

let test_LCspec (v0 v1 : vprop') (vx0 : int -> vprop')
  : lin_cond_r [v0; v1] (specT int [v0] (fun x -> [vx0 x]))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    build_LCspec test_flags None
  )

let test_LCret (v0 v1 : vprop') (vx0 : int -> vprop')
  : lin_cond_r [v0; v1; vx0 0] (M.Tret int 0 (fun x -> [v1; vx0 x]))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    build_LCret test_flags None
  )

let test_LCbind (v0 v1 v2 v3 : vprop') (vx0 vx1 : int -> vprop')
  : lin_cond_r [v0; v1; v2] (M.Tbind int int (specT int [v0] (fun x -> [v3; vx0 x]))
                                   (fun x -> specT int [vx0 x; v1] (fun y -> [vx1 y])))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    build_LCbind test_flags None
  )

let test_LCbindP_0 (v0 v1 : vprop') (vx0 : int -> vprop') (wp : pure_wp int)
  : lin_cond_r [v0; v1]
        (M.TbindP int int wp (fun x -> specT int [v0] (fun y -> [vx0 y])))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    build_LCbindP test_flags None
  )

let test_LCbindP_1 (v0 v1 : vprop') (vx0 : int -> vprop') (wp : pure_wp int)
  : lin_cond_r [v0; v1]
        (M.TbindP int int wp (fun x -> specT int [v0] (fun y -> [vx0 y])))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    apply (`LV.LCbindP);
    let x = intro () in
    build_lin_cond test_flags None
  )

[@@ expect_failure [228]]
let test_LCbindP_2 (vx0 : int -> vprop') (wp : pure_wp int)
  : lin_cond_r []
        (M.TbindP int int wp (fun x -> specT int [] (fun y -> [vx0 x])))
  = _ by (
    norm_test (); apply (`Mklin_cond_r);
    build_LCbindP test_flags None
  )


let test_lin_cond0 (v : int -> vprop') (vx : int -> int -> vprop')
  : LV.top_lin_cond
      (M.Tbind int int (specT int [v 0] (fun x -> [v 3; vx 0 x]))
             (fun x -> specT int [vx 0 x; v 1] (fun y -> [vx 1 y])))
      [v 0; v 1; v 2] (fun y -> [v 3; vx 1 y; v 2])
  = _ by (norm_test (); build_top_lin_cond test_flags)

let test_lin_cond1 (v : vprop') (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tbind int int (M.Tret int 0 (fun x -> [vx x]))
             (fun x -> M.Tret int x (fun x -> [vx x])))
      [v; vx 0] (fun x -> [v; vx x])
  = _ by (build_top_lin_cond test_flags)

/// This example succeeds thanks to the propagation of a production hind ([prd_hint]) which allows to use the top-level
/// post-condition to infer the dependency on [x] introduced by the [M.Tret].
let test_lin_cond__ret_hint0 (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tret int 0 (fun _ -> []))
      [vx 0] (fun x -> [vx x])
  = _ by (build_top_lin_cond test_flags)

let test_lin_cond__ret_hint1 (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tret int 0 (fun x -> [vx x]))
      [vx 0] (fun x -> [vx x])
  = _ by (build_top_lin_cond test_flags)

[@@ expect_failure [228]]
let test_lin_cond__ret_hint2 (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tbind int int
         (M.Tret int 0 (fun _ -> []))
         (fun x -> M.Tret int x (fun _ -> [])))
      [vx 0] (fun x -> [vx x])
  = _ by (build_top_lin_cond test_flags)

let test_lin_cond__ret_hint3 (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tbind int int
         (M.Tret int 0 (fun x -> [vx x]))
         (fun x -> M.Tret int x (fun _ -> [])))
      [vx 0] (fun x -> [vx x])
  = _ by (build_top_lin_cond test_flags)


[@@ expect_failure [228]]
let test_lin_cond__fail0 (v : int -> vprop')
  : LV.top_lin_cond
      (M.Tret int 0 (fun _ -> [v 1]))
      [v 0] (fun _ -> [v 1])
  = _ by (build_top_lin_cond test_flags)

[@@ expect_failure [228]]
let test_lin_cond__fail1 (vx : int -> vprop')
  : LV.top_lin_cond
      (M.Tbind int int (specT int [] (fun x -> [vx x]))
             (fun x -> M.Tret int 0 (fun _ -> [])))
      [] (fun x -> [])
  = _ by (norm_test (); build_top_lin_cond test_flags)


let test_lin_cond__if_0 (v0 v1 v2 : vprop')
  : LV.top_lin_cond
        (M.Tif _ true (specT int [v0] (fun _ -> [v1])) (specT int [v0] (fun _ -> [v1])))
        [v0; v2] (fun _ -> [v1; v2])
  = _ by (norm_test (); build_top_lin_cond test_flags)

let test_lin_cond__if_1 (v : int -> vprop')
  : LV.top_lin_cond
        (M.Tif _ true (specT int [v 0] (fun _ -> [v 0]))
                      (specT int [v 1] (fun _ -> [v 1])))
        [v 0; v 1; v 2] (fun _ -> [v 0; v 1; v 2])
  = _ by (norm_test (); build_top_lin_cond test_flags)

[@@ expect_failure [228]]
let test_lin_cond__if_2 (v : int -> vprop')
  : LV.top_lin_cond
        (M.Tif _ true (specT int [v 0] (fun _ -> [v 1]))
                      (specT int []    (fun _ -> [])))
        [v 0] (fun _ -> [v 1])
  = _ by (norm_test (); build_top_lin_cond test_flags)

[@@ expect_failure [228]]
let test_lin_cond__if_3 (vx : int -> vprop')
  : LV.top_lin_cond
        (M.Tbind int int
          (M.Tif _ true (M.Tret int 0 (fun _ -> []))
                        (M.Tret int 0 (fun _ -> [])))
          (fun x -> M.Tret int x (fun _ -> [])))
        [vx 0] (fun x -> [vx x])
  = _ by (norm_test (); build_top_lin_cond test_flags)

let test_lin_cond__if_3 (vx : int -> vprop')
  : LV.top_lin_cond
        (M.Tbind int int
          (M.Tif _ true (M.Tret int 0 (fun x -> [vx x]))
                        (M.Tret int 0 (fun _ -> [])))
          (fun x -> M.Tret int x (fun _ -> [])))
        [vx 0] (fun x -> [vx x])
  = _ by (norm_test (); build_top_lin_cond test_flags)

[@@ expect_failure [228]]
let test_lin_cond__if_4 (vx : int -> vprop')
  : LV.top_lin_cond
        (M.Tbind int int
          (M.Tif _ true (M.Tret int 0 (fun _ -> []))
                        (M.Tret int 0 (fun x -> [vx x])))
          (fun x -> M.Tret int x (fun _ -> [])))
        [vx 0] (fun x -> [vx x])
  = _ by (norm_test (); build_top_lin_cond test_flags)
