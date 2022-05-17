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
module CSl  = Experiment.Steel.CondSolver

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference
open Learn.Tactics.Util
open Experiment.Steel

irreducible let __test__ : unit = ()
let norm_test () = T.norm [delta_qualifier ["unfold"]; delta_attr [`%__test__]]

let clean () : Tactics.Tac unit =
  Learn.Tactics.Util.clear_all ();
  norm_test ()

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

(*let () = assert (U.print_util (ST.flatten_prog test_flatten))
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
  assert (U.print_util (Fun.elim_returns (Fun.can_lam Fun.can_tys) test_elim_returns test_elim_returns_shape))
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

let steel_read (r : ref nat) () :
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

[@@ __test__; __steel_reduce__]
let r_read (r : ref nat) : M.repr nat =
  M.repr_of_steel (read_pre r) (read_post r) (read_req r) (read_ens r) (steel_read r)

let steel_write (r : ref nat) (x : nat) ()
  : Steel unit (M.vprop_of_list [vptr' r full_perm]) (fun _ -> M.vprop_of_list [vptr' r full_perm])
               (requires fun _ -> True) (ensures fun h0 () h1 -> M.rmem_sels [vptr' r full_perm] h1 0 == x)
  =
    (**) change_equal_slprop (M.vprop_of_list [vptr' r full_perm]) (vptr r `star` emp);
    write r x;
    (**) change_equal_slprop (vptr r `star` emp) (M.vprop_of_list [vptr' r full_perm])

[@@ __test__; __steel_reduce__]
let r_write (r : ref nat) (x : nat) : M.repr unit =
  M.repr_of_steel [vptr' r full_perm] (fun _ -> [vptr' r full_perm])
                  (fun sl0 -> True) (fun sl0 () sl1 -> sl1 0 == x)
                  (steel_write r x)

[@@ __test__; __steel_reduce__]
let test0_M (r : ref nat) : M.repr nat = M.(
  x <-- r_read r;
  return x)

let normal_vp : list norm_step = [
    delta_only [`%L.map; `%L.append; `%L.op_At];
    delta_qualifier ["unfold"];
    iota; zeta_full
  ]

(*let _ = fun r ->
  assert (U.print_util (test0_M r).repr_tree) by T.(norm __normal_M; qed ())*)

unfold
let test0_equiv (r : ref nat) (v : vprop') : M.vequiv ([vptr' r full_perm; v]) [vptr' r full_perm; v] =
  Perm.id_n 2

[@@ __test__]
let test0_cond (r : ref nat) (v : vprop')
  : M.tree_cond (test0_M r).repr_tree [vptr' r full_perm; v] (fun _ -> [vptr' r full_perm; v])
  = _ by T.(
    norm __normal_M;
    apply (`M.TCbind);
     (apply (`(M.TCspec [vptr' (`@r) full_perm; (`@v)] (fun _ -> [vptr' (`@r) full_perm; (`@v)]) [(`@v)]));
       (norm normal_vp; exact (`test0_equiv (`@r) (`@v)));
       (let x = intro () in
        norm normal_vp; (* FIXME: @ is not unfolded *)
        exact (`test0_equiv (`@r) (`@v))));
     (let x = intro () in
      apply (`M.TCret);
       (norm normal_vp; exact (`test0_equiv (`@r) (`@v))));
  qed ())

[@@ __test__]
let test0_shape_M : M.shape_tree 2 2 = M.(
  Sbind _ _ _ (M.Sspec 1 1 1 (Perm.perm_f_to_list (Perm.id_n 2)) (Perm.perm_f_to_list (Perm.id_n 2)))
              (M.Sret 2 (Perm.perm_f_to_list (Perm.id_n 2))))

let normal_shape_M : list norm_step = [
    delta_only [`%M.tree_cond_has_shape; `%L.length; `%Perm.perm_f_to_list; `%Ll.list_eq; `%Ll.initi];
    delta_qualifier ["unfold"];
    iota; zeta; simplify; primops
  ]

let test0_M_has_shape (r : ref nat) (v : vprop')
  : squash (M.tree_cond_has_shape (test0_cond r v) test0_shape_M)
  = _ by T.(norm_test (); norm normal_shape_M; smt ())


[@@ __test__]
let test0_ST (r : ref nat) (v : vprop') =
  ST.flatten_prog (ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r v))

(*let _ = fun r ->
   assert (U.print_util (test0_ST r (to_vprop' Steel.Memory.emp)))
       by T.(norm_test ();
             norm __normal_ST;
             fail "print")*)

[@@ __test__]
let test0_shape_ST (r : ref nat) (v : vprop') : ST.prog_shape (test0_ST r v)
  = 
    (**) test0_M_has_shape r v;
    (**) ST.repr_ST_of_M_shape (test0_M r).repr_tree (test0_cond r v) test0_shape_M;
    let s = ST.shape_ST_of_M test0_shape_M in
    (**) ST.flatten_prog_shape (ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r v)) s;
    ST.mk_prog_shape (test0_ST r v) (ST.flatten_shape s)

(*let _ = fun r v ->
   assert (U.print_util (test0_shape_ST r v))
       by T.(norm_test (); norm __normal_ST; fail "print")*)

[@@ __test__]
let test0_SF (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) : SF.prog_tree _ _ =
  SF.repr_SF_of_ST (test0_ST r v) (test0_shape_ST r v) Fl.(cons x_ini (cons v_ini nil))

(*let _ = fun r (p : Steel.Memory.slprop) x_ini ->
    assert (U.print_util (test0_SF r (to_vprop' p) x_ini ()))
        by T.(clean ();
              norm __normal_ST;
              norm __normal_SF;
              fail "print")*)

[@@ __test__]
let test0_shape_SF (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) : SF.prog_shape (test0_SF r v x_ini v_ini)
  =
    (**) SF.repr_SF_of_ST_shape (test0_ST r v) (test0_shape_ST r v) Fl.(cons x_ini (cons v_ini nil));
    SF.mk_prog_shape (test0_SF r v x_ini v_ini) (SF.shape_SF_of_ST (test0_shape_ST r v).shp)

(*let _ = fun r v x_ini v_ini ->
  assert (U.print_util (test0_shape_SF r v x_ini v_ini))
    by T.(clean ();
          norm __normal_ST;
          norm __normal_SF;
          fail "print")*)


[@@ __test__]
let test0_Fun (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) = 
  SF.repr_Fun_of_SF (test0_SF r v x_ini v_ini)

(*let _ = fun r (p : Steel.Memory.slprop) x_ini ->
    assert (U.print_util (test0_Fun r (to_vprop' p) x_ini ()))
        by T.(clean ();
              norm __normal_ST;
              norm __normal_SF;
              norm __normal_Fun;
              fail "print")*)

(*let _ = fun r (p : Steel.Memory.slprop) x_ini ->
    let v = to_vprop' p in
    (**) SF.repr_Fun_of_SF_shape (test0_SF r v x_ini ()) (test0_shape_SF r v x_ini ());
    assert (U.print_util (Fun.elim_returns SF.sl_tys_lam (test0_Fun r v x_ini ())
                                         (SF.shape_Fun_of_SF (test0_shape_SF r v x_ini ()).shp)))
        by T.(clean ();
              let t = timer_start "normal_ST"  in
              norm __normal_ST;
              let t = timer_enter t "normal_SF"  in
              norm __normal_SF;
              let t = timer_enter t "normal_Fun" in
              norm __normal_Fun;
              let t = timer_enter t "elim_returns_0" in
              norm __normal_Fun_elim_returns_0;
              let t = timer_enter t "elim_returns_1" in
              norm __normal_Fun_elim_returns_1;
              timer_stop t;
              fail "print")*)

unfold
let test0_wp (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) =
  Fun.tree_wp (test0_Fun r v x_ini v_ini) (fun res -> res.val_v >= 0)

(*let _ = fun r p x_ini ->
    assert (U.print_util (test0_wp r (to_vprop' p) x_ini ()))
        by T.(clean ();
              norm __normal_ST;
              norm __normal_SF;
              norm __normal_Fun;
              norm __normal_Fun_spec;
              fail "print")*)


////////// test1 //////////

[@@ __test__]
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

[@@ __test__]
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
  = _ by T.(norm_test (); norm normal_shape_ST'; smt ())

[@@ __test__]
let test1_shape_ST : ST.prog_shape test1_ST =
  (**) test1_ST_has_shape ();
  ST.mk_prog_shape test1_ST test1_shape_tree_ST

[@@ __test__]
let test1_SF (b_ini : bool) (x_ini : int) : SF.prog_tree _ _ =
  SF.repr_SF_of_ST test1_ST test1_shape_ST Fl.(cons b_ini (cons x_ini nil))

(*let _ = fun b_ini x_ini ->
  assert (U.print_util (test1_SF b_ini x_ini))
    by T.(clean ();
          norm __normal_ST;
          norm __normal_SF;
          fail "print")*)

[@@ __test__]
let test1_Fun (b_ini : bool) (x_ini : int) = 
  SF.repr_Fun_of_SF (test1_SF b_ini x_ini)

(*let _ = fun b_ini x_ini ->
  assert (U.print_util (test1_Fun b_ini x_ini))
    by T.(clean ();
          norm __normal_ST;
          norm __normal_SF;
          norm __normal_Fun;
          fail "print")*)


////////// test2 //////////

[@@ __test__]
let test2_SF : SF.prog_tree bool (fun _ -> [int]) = SF.(
  Tbind bool bool (fun _ -> [int; int]) (fun _ -> [int])
    (Tspec bool (fun _ -> [int; int]) True
      (fun (b : bool) (xs : Fl.flist [int; int]) ->
         b ==> xs 0 + xs 1 >= 0))
    (fun (b : bool) (xs : Fl.flist [int; int]) ->
      Tret bool (b && xs 0 >= 0)
              (fun _ -> [int]) Dl.(DCons _ (xs 0 + xs 1) _ DNil)))

[@@ __test__]
let test2_Fun =
  SF.repr_Fun_of_SF test2_SF

(*let _ =
  assert (U.print_util test2_Fun)
    by T.(clean ();
          norm __normal_Fun;
          fail "print")*)

[@@ __test__]
let test2_wp =
  Fun.tree_wp test2_Fun (fun x -> b2t x.val_v)

(*#push-options "--print_full_names"
let _ =
  assert (U.print_util test2_wp)
    by T.(clean ();
          norm __normal_Fun;
          norm __normal_Fun_spec;
          fail "print")
#pop-options*)


////////// test3 //////////

[@@ __reduce__]
let test3_M (r0 r1 : ref nat) : M.repr unit = M.(
  x <-- r_read r0;
  r_write r1 (x + 1))

[@@ __reduce__]
let test3_mem (r0 r1 : ref nat) =
  [vptr' r0 full_perm; vptr' r1 full_perm]

inline_for_extraction
let test3_steel (r0 r1 : ref nat)
  : extract (test3_M r0 r1)
      (test3_mem r0 r1) (fun _ -> test3_mem r0 r1)
      (requires fun _ -> True) (ensures fun sl0 () sl1 -> sl1 1 == sl0 0 + 1)
  = _ by (solve_by_wp ())


(* TODO *)
(*let __normal_rmem_sels : list norm_step = [
  delta_only [`%M.rmem_sels; `%Fl.flist_of_d; `%M.rmem_sl_list; `%M.vpl_sels;
              `%Dl.index];
  delta_attr [`%__reduce__];
  iota; zeta;
]

(*module T = FStar.Tactics
[@@ handle_smt_goals ]
let tac () = T.dump "test"

let steel_subcomp
      (#a : Type) (#pre : pre_t) (#post : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : (h0 : rmem pre) ->
                Lemma (requires req_g h0) (ensures req_f h0))
      (pf_ens : (h0 : rmem pre) -> (x : a) -> (h1 : rmem (post x)) ->
                Lemma (requires req_f h0 /\ req_g h0 /\ ens_f h0 x h1) (ensures ens_g h0 x h1))
      (f : unit -> Steel a pre post req_f ens_f)
  : Steel a pre post req_g ens_g
  =
    (**) let h0 = get () in
    (**) pf_req h0;
    let x = f () in
    (**) let h1 = get () in
    (**) pf_ens h0 x h1;
    Steel.Effect.Atomic.return x*)

type unit_steel (a : Type) (pre : pre_t) (post : post_t a) (req : req_t pre) (ens : ens_t pre a post)
  = unit -> Steel a pre post req ens

let steel_subcomp_eq
      (#a : Type) (#pre : pre_t) (#post : post_t a)
      (req_f : req_t pre) (ens_f : ens_t pre a post)
      (req_g : req_t pre) (ens_g : ens_t pre a post)
      (pf_req : unit -> squash (req_f == req_g))
      (pf_ens : unit -> squash (ens_f == ens_g))
      (f : unit_steel a pre post req_f ens_f)
  : unit_steel a pre post req_g ens_g
  = pf_req ();
    pf_ens ();
    U.cast #(unit_steel a pre post req_f ens_f) (unit_steel a pre post req_g ens_g) f

let call_repr_steel
      (#a : Type)
      (#pre : M.pre_t)     (#post : M.post_t a)
      (#req : M.req_t pre) (#ens  : M.ens_t pre a post)
      (r : M.repr_steel_t a pre post req ens)
  : Steel a (M.vprop_of_list pre) (fun x -> M.vprop_of_list (post x))
      (requires fun h0      -> req (norm __normal_rmem_sels (M.rmem_sels pre h0)))
      (ensures  fun h0 x h1 -> ens (norm __normal_rmem_sels (M.rmem_sels pre h0))
                                x
                                (norm __normal_rmem_sels (M.rmem_sels (post x) h1)))
  =
    (**) let h0 = get () in
    assume False;
    r ()

    (*steel_subcomp_eq
      #a #(M.vprop_of_list pre) #(fun x -> M.vprop_of_list (post x))
      (fun h0 -> req (M.rmem_sels pre h0))
      (fun h0 x h1 -> ens (M.rmem_sels pre h0) x (M.rmem_sels (post x) h1))
      (fun h0 -> req (norm __normal_rmem_sels (M.rmem_sels pre h0)))
      (fun h0 x h1 -> ens (norm __normal_rmem_sels (M.rmem_sels pre h0))
                       x
                       (norm __normal_rmem_sels (M.rmem_sels (post x) h1)))
      (fun () -> admit ()) (fun () -> admit ())
      r*)

let test_3_steel_caller (r0 r1 : ref nat)
  : Steel nat (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == 5)
      (ensures fun h0 x h1 -> x == 6)
  =
    call_repr_steel (test3_steel r0 r1);
    read r1
*)
