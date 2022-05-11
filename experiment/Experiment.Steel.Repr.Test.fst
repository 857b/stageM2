module Experiment.Steel.Repr.Test

module U    = Learn.Util
module T    = FStar.Tactics
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module Perm = Learn.Permutation

module M    = Experiment.Steel.Repr.M
module ST   = Experiment.Steel.Repr.ST
module SF   = Experiment.Steel.Repr.SF
module Fun  = Experiment.Repr.Fun

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference


irreducible
let print_util (#a : Type) (x : a) : prop = True


////////// test_flatten //////////

unfold
let test_flatten : ST.prog_tree int [] (fun _ -> []) = ST.(
  x1 <-- (x0 <-- Tspec int [] (fun _ -> []) (fun _ -> True) (fun _ x _ -> x == 0);
        Tret int (x0 + 1) (fun _ -> []));
  Tret int (x1 + 2) (fun _ -> []))

let normal_flatten_prog : list norm_step = [
    delta_only [`%ST.flatten_prog; `%ST.flatten_prog_aux; `%ST.flatten_prog_k_id; `%ST.bind];
    delta_qualifier ["unfold"];
    iota; zeta
  ]

(*let () = assert (print_util (ST.flatten_prog test_flatten))
             by T.(norm normal_flatten_prog; fail "print")*)


////////// test_elim_returns //////////

let test_elim_returns : Fun.prog_tree #Fun.can_tys int = Fun.(
  (**) let wp pt = pt 1 in
  (**) FStar.Monotonic.Pure.intro_pure_wp_monotonicity wp;
  y <-- TbindP int int wp (fun () -> 1)
                     (fun x -> return (x + 1));
  return (y + 2))

unfold
let test_elim_returns_shape_tree : Fun.shape_tree = Fun.(
  Sbind (SbindP (Sret true)) (Sret true))

let test_elim_returns_shape : Fun.prog_shape #Fun.can_tys #int test_elim_returns
  =
    (**) assert (Fun.prog_has_shape' test_elim_returns test_elim_returns_shape_tree)
           by T.(norm [delta_only [`%Fun.prog_has_shape']; delta_qualifier ["unfold"]; zeta; iota; simplify];
                 smt ());
    test_elim_returns_shape_tree

let normal_elim_returns : list norm_step = [
    delta_only [`%Fun.elim_returns; `%Fun.elim_returns_aux; `%Fun.elim_returns_k_trm; `%Fun.elim_returns_k_ret;
                `%Fun.Mktys'?.v_of_r; `%Fun.Mktys'?.r_of_v;
                `%Fun.can_tys];
    delta_qualifier ["unfold"];
    iota; zeta
  ]

(*let () =
  assert (print_util (Fun.elim_returns (Fun.can_lam Fun.can_tys) test_elim_returns test_elim_returns_shape))
    by T.(norm [delta_only [`%test_elim_returns; `%test_elim_returns_shape]];
          norm normal_elim_returns;
          fail "print")*)


////////// test0 //////////

unfold
let read_pre  (r : ref nat) : M.pre_t
  = [vptr' r full_perm]
unfold
let read_post (r : ref nat) : M.post_t nat
  = fun _ -> [vptr' r full_perm]
unfold
let read_req  (r : ref nat) : M.req_t (read_pre r)
  = fun sl0 -> True
unfold
let read_ens  (r : ref nat) : M.ens_t (read_pre r) nat (read_post r)
  = fun sl0 x sl1 ->
    sl1 0 == sl0 0 /\ x == sl0 0

let steel_read0 (r : ref nat) () :
  Steel nat (M.vprop_of_list [vptr' r full_perm]) (fun _ -> M.vprop_of_list [vptr' r full_perm])
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> let sl0 = M.rmem_sels [vptr' r full_perm] h0 in
                         let sl1 = M.rmem_sels [vptr' r full_perm] h1 in
                         sl1 0 == sl0 0 /\ x == sl0 0)
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
let test0_ST (r : ref nat) = ST.flatten_prog (ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r))

let normal_tree_ST : list norm_step = [
    delta_only [`%ST.repr_ST_of_M; `%ST.bind; `%ST.post_ST_of_M; `%M.vprop_list_sels_t;
                `%L.map; `%Mkvprop'?.t; `%ST.const_post; `%ST.frame_post; `%L.op_At; `%L.append;
                `%ST.flatten_prog; `%ST.flatten_prog_aux; `%ST.flatten_prog_k_id];
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
    let s = ST.shape_ST_of_M test0_shape_M in
    (**) ST.flatten_prog_shape (ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r)) s;
    ST.mk_prog_shape (test0_ST r) (ST.flatten_shape s)

let normal_shape_ST : list norm_step = [
    delta_only [`%ST.shape_ST_of_M; `%ST.flatten_shape; `%ST.flatten_shape_aux; `%ST.flatten_shape_k_id];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ = fun r ->
   assert (print_util (test0_shape_ST r))
       by T.(norm normal_shape_ST; qed ())*)

unfold
let test0_SF (r : ref nat) (x_ini : nat) : SF.prog_tree _ _ =
  SF.repr_SF_of_ST (test0_ST r) (test0_shape_ST r) Fl.(cons x_ini nil)

let normal_tree_SF : list norm_step = [
    delta_only [`%SF.repr_SF_of_ST; `%SF.shape_SF_of_ST;
                `%SF.post_SF_of_ST; `%SF.postl_SF_of_ST; `%SF.post_bij;
                `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
                `%SF.Mkpost_bij_t'?.len_SF; `%SF.Mkpost_bij_t'?.idx_SF; `%SF.Mkpost_bij_t'?.idx_ST;
                `%Ll.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%L.length;
                `%SF.sel_ST_of_SF; `%SF.sell_ST_of_SF; `%SF.post_src_of_shape;
                `%SF.post_src_f_of_shape; `%SF.sel_SF_of_ST; `%SF.sell_SF_of_ST;
                `%Fl.splitAt_ty; `%Fl.head; `%Fl.tail;
                `%Fl.dlist_of_f; `%Dl.initi;
                `%Mktuple2?._1;`%Mktuple2?._2;
                `%Learn.Option.map;
                `%Perm.perm_f_swap; `%Perm.perm_f_transpose; `%Perm.perm_f_of_pair;
                `%Perm.mk_perm_f; `%Perm.id_n];
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
let test0_shape_SF (r : ref nat) (x_ini : nat) : SF.prog_shape (test0_SF r x_ini)
  =
    (**) SF.repr_SF_of_ST_shape (test0_ST r) (test0_shape_ST r) Fl.(cons x_ini nil);
    SF.mk_prog_shape (test0_SF r x_ini) (SF.shape_SF_of_ST (test0_shape_ST r).shp)

(*let _ = fun r x_ini ->
  assert (print_util (test0_shape_SF r x_ini))
    by T.(norm normal_shape_ST;
          norm normal_tree_SF;
          fail "print")*)


unfold
let test0_Fun (r : ref nat) (x_ini : nat) = 
  SF.repr_Fun_of_SF (test0_SF r x_ini)

let normal_repr_Fun_of_SF : list norm_step = [
    delta_only [`%SF.repr_Fun_of_SF];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ = fun r x_ini ->
    assert (print_util (test0_Fun r x_ini))
        by T.(norm normal_tree_ST;
              norm normal_shape_ST;
              norm normal_tree_SF;
              norm normal_repr_Fun_of_SF;
              qed ())*)

let normal_shape_Fun : list norm_step = [
    delta_only [`%SF.shape_Fun_of_SF; `%SF.Mkprog_shape?.post_len; `%SF.Mkprog_shape?.shp];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

let normal_Fun_elim_returns : list norm_step = [
    delta_only [`%Fun.elim_returns; `%Fun.elim_returns_aux; `%Fun.elim_returns_k_trm; `%Fun.elim_returns_k_ret;
                `%SF.sl_tys; `%SF.sl_tys_lam;
                `%Fun.Mktys'?.v_of_r; `%Fun.Mktys'?.r_of_v;
                `%Fun.Mktys_lam'?.lam_prop; `%Fun.Mktys_lam'?.lam_tree;
                `%SF.Mksl_tys_t?.val_t;     `%SF.Mksl_tys_t?.sel_t;
                `%SF.Mksl_tys_v?.val_v;     `%SF.Mksl_tys_v?.sel_v;
                `%SF.Mksl_tys_r?.vl;        `%SF.Mksl_tys_r?.sl;
                `%Fun.Tret?.x;
                `%SF.sl_v_of_r; `%SF.sl_r_of_v
                ];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

let normal_after_Fun_elim_returns : list norm_step = [
    delta_only [`%SF.delayed_sl_uncurrify;
                `%Fl.cons; `%Fl.nil; `%Fl.dlist_of_f; `%Fl.flist_of_d; `%Dl.initi; `%Dl.index;
                `%L.length; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%Ll.initi];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ = fun r x_ini ->
    (**) SF.repr_Fun_of_SF_shape (test0_SF r x_ini) (test0_shape_SF r x_ini);
    assert (print_util (Fun.elim_returns SF.sl_tys_lam (test0_Fun r x_ini)
                                         (SF.shape_Fun_of_SF (test0_shape_SF r x_ini).shp)))
        by T.(U.clear_all ();
              norm normal_tree_ST;
              norm normal_shape_ST;
              norm normal_tree_SF;
              norm normal_repr_Fun_of_SF;
              norm normal_shape_Fun;
              norm normal_Fun_elim_returns;
              norm normal_after_Fun_elim_returns;
              fail "print")*)

unfold
let test0_wp (r : ref nat) (x_ini : nat) =
  Fun.tree_wp (test0_Fun r x_ini) (fun res -> res.val_v >= 0)

let normal_spec_Fun : list norm_step = [
    delta_only [`%Fun.tree_wp; `%Fl.partial_app_flist;
                `%Fun.Mktys'?.all; `%SF.sl_tys; `%SF.sl_all; `%Fl.forall_flist;
                `%Fun.Mktys'?.v_of_r; `%SF.sl_v_of_r;
                `%Fl.cons; `%Fl.nil;
                `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t;
                `%SF.Mksl_tys_v?.val_v; `%SF.Mksl_tys_v?.sel_v;
                `%SF.Mksl_tys_r?.vl; `%SF.Mksl_tys_r?.sl];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ = fun r x_ini ->
    assert (print_util (test0_wp r x_ini))
        by T.(norm normal_tree_ST;
              norm normal_shape_ST;
              norm normal_tree_SF;
              norm normal_repr_Fun_of_SF;
              norm normal_spec_Fun;
              qed ())*)


////////// test1 //////////

unfold
let test1_ST : ST.prog_tree int [bool; int] (fun _ -> [bool; int])
  = ST.(
    b <-- Tframe _ _ _ [int] (
           Tspec bool [bool] (fun _ -> [bool])
             (fun _ -> True) (fun sl0 b sl1 -> sl1 0 = sl0 0 /\ b = sl0 0));
    Tequiv [bool; int] [int; bool] (Perm.perm_f_swap #2 0);;
    x <-- Tframe _ _ _ [bool] (Tspec int [int] (fun _ -> [int])
           (fun _ -> True) (fun sl0 x sl1 -> sl1 0 = sl0 0 /\ x = sl0 0));
    Tequiv [int; bool] [bool; int] (Perm.perm_f_swap #2 0);;
    Tret int (if b then x else 0) (fun _ -> [bool; int])
  )

unfold
let test1_shape_tree_ST : ST.shape_tree 2 2 = ST.(
  Sbind _ _ _ (Sframe _ _ 1 (Sspec  1 1))
 (Sbind _ _ _ (Sequiv 2 (Perm.perm_f_swap #2 0))
 (Sbind _ _ _ (Sframe _ _ 1 (Sspec  1 1))
 (Sbind _ _ _ (Sequiv 2 (Perm.perm_f_swap #2 0))
              (Sret   true 2)))))


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
  SF.repr_SF_of_ST test1_ST test1_shape_ST Fl.(cons b_ini (cons x_ini nil))

let norm_test_Fun : list norm_step
  = [delta_only [`%ST.bind; `%L.length; `%L.op_At; `%L.append];
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

let delta_only_repr_SF_of_ST =
  [`%SF.repr_SF_of_ST; `%ST.match_prog_tree;
   `%SF.post_SF_of_ST; `%Learn.List.initi; `%L.index; `%L.hd; `%L.tl; `%L.tail; `%L.op_At; `%L.append;
   `%SF.Mkpost_bij_t'?.len_SF; `%SF.Mkpost_bij_t'?.idx_SF; `%SF.Mkpost_bij_t'?.idx_ST;
   `%ST.Mkprog_shape?.post_len; `%ST.Mkprog_shape?.shp;
   `%SF.post_bij; `%SF.sel_ST_of_SF; `%SF.sel_SF_of_ST; `%SF.post_src_of_shape;
   `%ST.frame_post; `%ST.const_post]

let norm_repr_SF_of_ST1 : list norm_step
  = [delta_only delta_only_repr_SF_of_ST;
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

(*let _ = fun b_ini x_ini ->
  assert (print_util (test1_SF b_ini x_ini))
    by T.(norm norm_test_Fun;
          norm norm_repr_Fun_of_ST1;
          qed ())*)

unfold
let test1_Fun (b_ini : bool) (x_ini : int) = 
  SF.repr_Fun_of_SF (test1_SF b_ini x_ini)

let norm_repr_Fun_of_SF : list norm_step
  = [delta_only (L.append delta_only_repr_SF_of_ST
                [`%SF.repr_Fun_of_SF; `%Fl.partial_app_flist;
                 `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t;
                 `%Mktuple2?._1; `%Mktuple2?._2;
                 `%L.length;

                 `%Perm.perm_f_swap; `%Perm.perm_f_transpose; `%Perm.perm_f_of_pair;
                 `%Perm.mk_perm_f]);
     delta_qualifier ["unfold"];
     delta_attr [`%U.__util_func__];
     iota; zeta; primops]

(*let _ = fun b_ini x_ini ->
  assert (print_util (test1_Fun b_ini x_ini))
    by T.(norm norm_test_Fun;
          norm norm_repr_Fun_of_ST;
          norm norm_repr_Fun_of_SF;
          qed ())*)


////////// test2 //////////

unfold
let test2_SF : SF.prog_tree bool (fun _ -> [int]) = SF.(
  Tbind bool bool (fun _ -> [int; int]) (fun _ -> [int])
    (Tspec bool (fun _ -> [int; int]) True
      (fun (b : bool) (xs : Fl.flist [int; int]) ->
         b ==> xs 0 + xs 1 >= 0))
    (fun (b : bool) (xs : Fl.flist [int; int]) ->
      Tret bool (b && xs 0 >= 0)
              (fun _ -> [int]) Dl.(DCons _ (xs 0 + xs 1) _ DNil)))

unfold
let test2_Fun =
  SF.repr_Fun_of_SF test2_SF

let normal_tree_Fun : list norm_step = [
    delta_only [`%SF.repr_Fun_of_SF; `%Fl.partial_app_flist;
                `%SF.Mksl_tys_t?.val_t; `%SF.Mksl_tys_t?.sel_t];
    delta_qualifier ["unfold"];
    iota; zeta; primops
  ]

(*let _ =
  assert (print_util test2_Fun)
    by T.(norm normal_tree_Fun;
          qed ())*)


unfold
let test2_wp =
  Fun.tree_wp test2_Fun (fun x -> b2t x.val_v)

(*#push-options "--print_full_names"
let _ =
  assert (print_util test2_wp)
    by T.(norm normal_tree_Fun;
          norm normal_spec_Fun;
          qed ())
#pop-options*)
