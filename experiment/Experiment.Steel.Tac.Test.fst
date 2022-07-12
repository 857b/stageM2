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


let test_build_hpred_to_vpl (r r' : ref nat)
    (_ : squash ((vptr r `star` vptr r') `equiv` vprop_of_list [vptr' r full_perm; vptr' r' full_perm]))
  : hpred_to_vpl (vptr r `star` vptr r') [vptr' r full_perm; vptr' r' full_perm]
                 (fun h -> sel r h + sel r' h < 10 <: Type0)
  = _ by (build_hpred_to_vpl test_flags dummy_ctx)

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
  = M.Tspec a (M.spec_r_exact (M.Mkspec_r pre post [] (fun _ _ -> True) (fun _ _ _ _ -> True)))

let rec repeat_n (n : nat) (t : M.prog_tree unit) : M.prog_tree unit
  = if n = 0 then M.Tret unit () (fun _ -> [])
    else M.Tbind unit unit t (fun () -> repeat_n (n-1) t)

let norm_test () : Tac unit
  = norm [delta_only [`%repeat_n; `%Ll.initi];
          delta_qualifier ["unfold"];
          iota; zeta; primops]


(**** [spec_find_ro], [spec_r] *)

noeq
type test_build_arg (#a : Type) ($f : a -> Type) : Type =
  | TestBuildArg : (x : a) -> (y : f x) -> test_build_arg f

#push-options "--fuel 3"
let test_ens_refl_0
      (r0 r1 : ref nat)
      (sl0 : sl_f [vptr' r0 full_perm; vptr' r1 full_perm])
      (sl1 : sl_f [vptr' r0 full_perm; vptr' r1 full_perm])
  : test_build_arg (ens_refl sl0 sl1 (sl1 0 == sl0 0 /\ sl1 1 == sl0 0 + sl0 1))
  = _ by (apply (`TestBuildArg);
          build_ens_refl ())

(*
let print_test_ens_refl_0 : U.print_util test_ens_refl_0
  = _ by (norm [delta_only [`%test_ens_refl_0]; delta_attr [`%__tac_helper__]];
          fail "print")
*)

let test_find_ro_0 (r0 r1 : ref nat)
  : M.spec_find_ro nat
      [vptr' r0 full_perm; vptr' r1 full_perm] (fun _ -> [vptr' r0 full_perm; vptr' r1 full_perm])
      (fun sl0 -> sl0 0 >= 0) (fun sl0 x sl1 -> sl1 0 == sl0 0 /\ sl1 0 == x)
  = _ by (build_spec_find_ro ())

(*
let print_test_fin_ro_0 : U.print_util test_find_ro_0
  = _ by (norm [delta_only [`%test_find_ro_0]; delta_attr [`%__tac_helper__]];
          fail "print")
 *)

#pop-options

let test_build_spec_r_0 (r0 r1 : ref nat)
  : test_build_arg (
      M.spec_r_steel #nat (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
         (fun h0 -> sel r0 h0 >= 0) (fun h0 x h1 -> sel r0 h1 == sel r0 h0 /\ sel r1 h1 == x))
  = _ by (apply (`TestBuildArg);
          build_spec_r default_flags dummy_ctx)

let test_build_spec_r_0_ro r0 r1 =
  assert ((M.SpecSteel?.sr (TestBuildArg?.y (test_build_spec_r_0 r0 r1))).M.sro_spc.spc_ro == [vptr' r0 full_perm])
    by (trefl ())

let test_build_spec_r_1 (r0 r1 : ref nat)
  : test_build_arg (
      M.spec_r_steel #nat (vptr r0 `star` vptr r1) (fun _ -> vptr r1 `star` vptr r0)
         (fun h0 -> sel r0 h0 >= 0) (fun h0 x h1 -> sel r1 h0 == sel r1 h1 /\ sel r0 h1 == sel r0 h0))
  = _ by (apply (`TestBuildArg);
          build_spec_r default_flags dummy_ctx)

(* the ensures should be just [True]
let print_test_build_spec_r_1 : U.print_util test_build_spec_r_1
  = _ by (norm [delta_only (L.append __delta_list [`%test_build_spec_r_1]);
                delta_attr [`%__tac_helper__]; iota; zeta; primops];
          fail "print")
*)

let test_build_spec_r_1_ro r0 r1 =
  assert ((M.SpecSteel?.sr (TestBuildArg?.y (test_build_spec_r_1 r0 r1))).M.sro_spc.spc_ro
       == [vptr' r0 full_perm; vptr' r1 full_perm])
    by (clear_all ();
        norm [delta_only [`%test_build_spec_r_0; `%TestBuildArg?.y; `%M.SpecSteel?.sr;
                          `%M.Mkspec_find_ro?.sro_spc; `%M.Mkspec_r?.spc_ro];
              delta_attr [`%__tac_helper__];
              iota];
        trefl ())


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
