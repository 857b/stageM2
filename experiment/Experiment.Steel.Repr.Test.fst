module Experiment.Steel.Repr.Test

module U    = Learn.Util
module T    = FStar.Tactics
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Perm = Learn.Permutation

module M    = Experiment.Steel.Repr.M
module ST   = Experiment.Steel.Repr.ST
module SF   = Experiment.Steel.Repr.Fun
module Fun  = Experiment.Repr.Fun

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference


irreducible
let print_util (#a : Type) (x : a) : prop = True


unfold
let read_pre  (r : ref nat) : M.pre_t
  = [vptr' r full_perm]
unfold
let read_post (r : ref nat) : M.post_t nat
  = fun _ -> [vptr' r full_perm]
let read_req  (r : ref nat) : M.req_t (read_pre r)
  = fun sl0 -> True
let read_ens  (r : ref nat) : M.ens_t (read_pre r) nat (read_post r)
  = fun sl0 x sl1 ->
    assert (L.length (M.vprop_list_sels_t (read_post r x)) == 1)
      by T.(trefl ());
    Dl.index sl1 0 == Dl.index sl0 0 /\ x == Dl.index sl0 0

let steel_read0 (r : ref nat) () :
  Steel nat (M.vprop_of_list [vptr' r full_perm]) (fun _ -> M.vprop_of_list [vptr' r full_perm])
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> let sl0 = M.rmem_sels [vptr' r full_perm] h0 in
                         let sl1 = M.rmem_sels [vptr' r full_perm] h1 in
                         Dl.index sl1 0 == Dl.index sl0 0 /\ x == Dl.index sl0 0)
  =
    (**) change_equal_slprop (M.vprop_of_list [vptr' r full_perm]) (vptr r `star` emp);
    let x = read r in
    (**) change_equal_slprop (vptr r `star` emp) (M.vprop_of_list [vptr' r full_perm]);
    Steel.Effect.Atomic.return x

let steel_read (r : ref nat)
  : M.repr_steel_t nat (read_pre r) (read_post r) (read_req r) (read_ens r)
  = U.cast_by (M.repr_steel_t nat (read_pre r) (read_post r) (read_req r) (read_ens r))
            (steel_read0 r)
            (_ by T.(trefl ()))

unfold let r_read (r : ref nat) : M.repr nat =
  M.repr_of_steel (read_pre r) (read_post r) (read_req r) (read_ens r) (steel_read r)


unfold
let test0_M (r : ref nat) : M.repr nat = M.(
  x <-- r_read r;
  return x)

let normal_tree_steps : list norm_step = [
    delta_attr [`%M.__tree_reduce__];
    delta_qualifier ["unfold"];
    delta_only [`%M.Mkrepr?.repr_tree];
    iota; zeta
  ]

let normal_vp : list norm_step = [
    delta_only [`%L.map; `%L.append; `%L.op_At; `%U.app_on];
    delta_qualifier ["unfold"];
    iota; zeta_full
  ]

(*let _ = fun r ->
  assert (print_util (test r).repr_tree) by T.(norm normal_tree_steps; qed ())*)

unfold
let test0_equiv (r : ref nat) : M.vequiv ([vptr' r full_perm]) [vptr' r full_perm] =
  Perm.id_n 1

unfold
let test0_cond (r : ref nat)
  : M.tree_cond (test0_M r).repr_tree [vptr' r full_perm] (fun _ -> [vptr' r full_perm])
  = _ by T.(
    apply (`M.TCbind);
     (apply (`(M.TCspec _ (read_post (`@r)) []));
       (norm normal_vp; exact (`test0_equiv (`@r)));
       (let x = intro () in
        norm normal_vp; (* TODO: @ is not unfolded *)
        exact (`test0_equiv (`@r))));
     (let x = intro () in
      apply (`M.TCret);
       (norm normal_vp; exact (`test0_equiv (`@r))));
  qed ())

unfold
let test0_shape_M : M.shape_tree 1 1 = M.(
  Sbind _ _ _ (M.Sspec 1 1 0 (Perm.id_n 1) (Perm.id_n 1))
              (M.Sret 1 (Perm.id_n 1)))

let normal_shape_M : list norm_step = [
    delta_only [`%M.tree_cond_has_shape; `%L.length];
    delta_qualifier ["unfold"];
    iota; zeta; simplify; primops
  ]

let test0_M_has_shape (r : ref nat)
  : squash (M.tree_cond_has_shape (test0_cond r) test0_shape_M)
  = _ by T.(norm normal_shape_M; smt ())


unfold
let test0_ST (r : ref nat) = ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r)

let normal_tree_ST : list norm_step = [
    delta_only [`%ST.repr_ST_of_M; `%ST.bind; `%ST.post_ST_of_M; `%M.vprop_list_sels_t;
                `%L.map; `%Mkvprop'?.t; `%ST.const_post; `%ST.frame_post; `%L.op_At; `%L.append];
    delta_qualifier ["unfold"];
    delta_attr [`%__steel_reduce__];
    iota; zeta; primops
  ]

(*let _ = fun r ->
   assert (print_util (test0_ST r))
       by T.(norm normal_tree_ST; qed ())*)

unfold
let test0_shape_ST (r : ref nat) : ST.prog_shape (test0_ST r)
  = 
    (**) test0_M_has_shape r;
    (**) ST.repr_ST_of_M_shape (test0_M r).repr_tree (test0_cond r) test0_shape_M;
    ST.mk_prog_shape (test0_ST r) (ST.shape_ST_of_M test0_shape_M)

let normal_shape_ST : list norm_step = [
    delta_only [`%ST.shape_ST_of_M];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ = fun r ->
   assert (print_util (test0_shape_ST r))
       by T.(norm normal_shape_ST; qed ())*)

unfold
let test0_SF (r : ref nat) (x_ini : nat) : SF.prog_tree _ _ =
  SF.repr_Fun_of_ST (test0_ST r) (test0_shape_ST r) Dl.(DCons _ x_ini _ DNil)

let normal_tree_SF : list norm_step = [
    delta_only [`%SF.repr_Fun_of_ST; `%SF.post_Fun_of_ST; `%SF.post_bij;
                `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
                `%SF.Mkpost_bij_t'?.post'_n; `%SF.Mkpost_bij_t'?.post'_f; `%SF.Mkpost_bij_t'?.post'_g;
                `%Ll.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail;
                `%SF.sel_ST_of_Fun; `%SF.post_src_of_shape];
    delta_qualifier ["unfold"];
    delta_attr [`%U.__util_func__];
    iota; zeta; primops
  ]

(*let _ = fun r x_ini ->
    assert (print_util (test0_SF r x_ini))
        by T.(norm normal_tree_ST;
              norm normal_shape_ST;
              norm normal_tree_SF;
              qed ())*)


unfold
let test1_ST : ST.prog_tree int [bool; int] (fun _ -> [bool; int])
  = ST.(
    b <-- Tspec bool [bool] (fun _ -> [bool]) [int]
           (fun _ -> True) (fun sl0 b sl1 -> Dl.index sl1 0 = Dl.index sl0 0 /\ b = Dl.index sl0 0);
    Tequiv [bool; int] [int; bool] (Perm.perm_f_swap #2 0);;
    x <-- Tspec int [int] (fun _ -> [int]) [bool]
           (fun _ -> True) (fun sl0 x sl1 -> Dl.index sl1 0 = Dl.index sl0 0 /\ x = Dl.index sl0 0);
    Tequiv [int; bool] [bool; int] (Perm.perm_f_swap #2 0);;
    Tret int (if b then x else 0) (fun _ -> [bool; int])
  )

unfold
let test1_shape_tree_ST : ST.shape_tree 2 2 = ST.(
  Sbind _ _ _ (Sspec  1 1 1)
 (Sbind _ _ _ (Sequiv 2 (Perm.perm_f_swap #2 0))
 (Sbind _ _ _ (Sspec  1 1 1)
 (Sbind _ _ _ (Sequiv 2 (Perm.perm_f_swap #2 0))
              (Sret   2)))))


let normal_shape_ST' : list norm_step = [
    delta_only [`%ST.prog_has_shape'; `%ST.bind; `%L.length];
    delta_qualifier ["unfold"];
    iota; zeta; primops; simplify
  ]

let test1_ST_has_shape () : squash (ST.prog_has_shape' test1_ST test1_shape_tree_ST)
  = _ by T.(norm normal_shape_ST'; smt ())

unfold
let test1_shape_ST : ST.prog_shape test1_ST =
  (**) test1_ST_has_shape ();
  ST.mk_prog_shape test1_ST test1_shape_tree_ST

unfold
let test1_SF (b_ini : bool) (x_ini : int) : SF.prog_tree _ _ =
  SF.repr_Fun_of_ST test1_ST test1_shape_ST Dl.(DCons _ b_ini _ (DCons _ x_ini _ DNil))

let norm_test_Fun : list norm_step
  = [delta_only [`%ST.bind; `%L.length; `%L.op_At; `%L.append];
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

let delta_only_repr_Fun_of_ST =
  [`%SF.repr_Fun_of_ST; `%ST.match_prog_tree;
   `%SF.post_Fun_of_ST; `%Learn.List.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%L.op_At; `%L.append;
   `%SF.Mkpost_bij_t'?.post'_n; `%SF.Mkpost_bij_t'?.post'_f; `%SF.Mkpost_bij_t'?.post'_g;
   `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
   `%SF.post_bij; `%SF.sel_ST_of_Fun; `%SF.sel_Fun_of_ST; `%SF.post_src_of_shape;
   `%ST.frame_post; `%ST.const_post]

let norm_repr_Fun_of_ST : list norm_step
  = [delta_only delta_only_repr_Fun_of_ST;
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

(*let _ = fun b_ini x_ini ->
  assert (print_util (test1_SF b_ini x_ini))
    by T.(norm norm_test_Fun;
          norm norm_repr_Fun_of_ST;
          qed ())*)

let test1_Fun (b_ini : bool) (x_ini : int) = 
  SF.repr_Fun_of_Steel (test1_SF b_ini x_ini)

let norm_repr_Fun_of_Steel : list norm_step
  = [delta_only (L.append delta_only_repr_Fun_of_ST
                [`%SF.repr_Fun_of_Steel; `%SF.sl_lam; `%SF.lam_dlist; `%SF.partial_app_dlist;
                 `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t;
                 `%Dl.index; `%Dl.splitAt_ty; `%Mktuple2?._1; `%Mktuple2?._2;
                 `%Dl.initi; `%L.length;
                 
                 `%Perm.perm_f_swap; `%Perm.perm_f_transpose; `%Perm.perm_f_of_pair;
                 `%Perm.mk_perm_f]);
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

(*let _ = fun b_ini x_ini ->
  assert (M.print_util (test_Fun' b_ini x_ini))
    by T.(norm [delta_only [`%test_Fun']];
          norm norm_test_Fun;
          norm norm_repr_Fun_of_ST;
          norm norm_repr_Fun_of_Steel;
          qed ())*)
