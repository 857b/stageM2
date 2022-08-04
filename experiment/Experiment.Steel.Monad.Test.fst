module Experiment.Steel.Monad.Test

module U    = Learn.Util
module T    = FStar.Tactics
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module SU   = Learn.Steel.Util
module U32  = FStar.UInt32
module Perm = Learn.Permutation

module F      = Experiment.Steel.Monad
module M      = Experiment.Steel.Repr.M
module MC     = Experiment.Steel.Combinators
module ST     = Experiment.Steel.Repr.ST
module LV     = Experiment.Steel.Repr.LV
module SF     = Experiment.Steel.Repr.SF
module SH     = Experiment.Steel.Steel
module Fun    = Experiment.Repr.Fun
module Vpl    = Experiment.Steel.VPropList
module Veq    = Experiment.Steel.VEquiv
module GCb    = Experiment.Steel.GCombinators
module Itf    = Experiment.Steel.Interface
module ST2SF  = Experiment.Steel.Repr.ST_to_SF.Spec
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference
open Learn.Tactics.Util
open Experiment.Steel

#push-options "--ide_id_info_off"

irreducible let __test__ : unit = ()
let norm_test () = T.norm [delta_qualifier ["unfold"]; delta_attr [`%__test__]]

let clean () : Tactics.Tac unit =
  Learn.Tactics.Util.clear_all ();
  norm_test ()


////////// simple full test //////////

//[@@ handle_smt_goals ]
//let tac () = T.dump "SMT query"

//#push-options "--z3refresh --query_stats"
//#push-options "--print_implicits"

inline_for_extraction
let test3_LV' (r0 r1 : ref U32.t)
  : F.usteel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel #[Timer; Extract; Dump Stage_Extract] (
      x <-- call read r0;
      call (write r1) U32.(x +%^ 1ul)
    ) ())
// time specs     : 95ms
// time lin_cond  : 276ms
// time sub_push  : 52ms
// time LV2SF     : 19ms
// time SF2Fun    : 4ms
// time Fun_wp    : 15ms
// time extract   : 186ms
// total time : 647ms [450ms-750ms]


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
  y <-- TbindP int int wp (fun x -> return (x + 1));
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
let read_pre : M.pre_t
  = []
unfold
let read_post #a : M.post_t a
  = fun _ -> []
unfold
let read_ro #a (r : ref a) : Vpl.vprop_list
  = [vptr' r full_perm]
unfold
let read_req  #a (r : ref a) (sl0 : Vpl.sl_f []) (sl_ro : Vpl.sl_f (read_ro r)) : Type0
  = True
unfold
let read_ens  #a (r : ref a) (sl0 : Vpl.sl_f []) (x : a) (sl1 : Vpl.sl_f []) (sl_ro : Vpl.sl_f (read_ro r)) : Type0
  = x == sl_ro 0

inline_for_extraction
let steel_read #a (r : ref a) () :
  Steel a (Vpl.vprop_of_list [] `star` Vpl.vprop_of_list [vptr' r full_perm])
    (fun _ -> Vpl.vprop_of_list [] `star` Vpl.vprop_of_list [vptr' r full_perm])
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> let sl_ro0 = Vpl.sel_f [vptr' r full_perm] h0 in
                         let sl_ro1 = Vpl.sel_f [vptr' r full_perm] h1 in
                         sl_ro1 == sl_ro0 /\ x == sl_ro0 0)
  =
    (**) Vpl.elim_vpl_cons (vptr' r full_perm) [];
    let x = read r in
    (**) Vpl.intro_vpl_cons (vptr' r full_perm) [];
    Steel.Effect.Atomic.return x

[@@ __test__; __reduce__; Itf.__repr_M__]
inline_for_extraction
let r_read (#a : Type0) (r : ref a) : M.repr SH.KSteel a =
  MC.repr_of_steel_r (M.Mkspec_r read_pre read_post (read_ro r) (read_req r) (read_ens r))
                     (SH.steel_f (steel_read r))

inline_for_extraction
let steel_write #a (r : ref a) (x : a) ()
  : Steel unit (Vpl.vprop_of_list [vptr' r full_perm] `star` Vpl.vprop_of_list [])
      (fun _ -> Vpl.vprop_of_list [vptr' r full_perm] `star` Vpl.vprop_of_list [])
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> x == Vpl.sel_f [vptr' r full_perm] h1 0 /\ Vpl.sel_f [] h1 == Vpl.sel_f [] h0)
  =
    (**) Vpl.elim_vpl_cons (vptr' r full_perm) [];
    write r x;
    (**) Vpl.intro_vpl_cons (vptr' r full_perm) []

[@@ __test__; __reduce__; Itf.__repr_M__]
inline_for_extraction
let r_write #a (r : ref a) (x : a) : M.repr SH.KSteel unit =
  MC.repr_of_steel_r (M.Mkspec_r [vptr' r full_perm] (fun _ -> [vptr' r full_perm]) []
                                 (fun sl0 sl_ro -> True) (fun sl0 () sl1 sl_ro -> x == sl1 0))
                    (SH.steel_f (steel_write r x))

////////// test1 //////////

let sequiv_of_perm (#pre #post : Fl.ty_list) (f : Perm.pequiv pre post) : ST.sequiv pre post = {
  seq_req = (fun _ -> True);
  seq_ens = (fun _ _ -> True);
  seq_eq  = Veq.mk_veq_eq (L.length pre) (L.length post) (fun i -> Some (f i));
  seq_typ = ()
}

[@@ __test__]
let test1_ST : ST.prog_tree int [bool; int] (fun _ -> [bool; int])
  = ST.(
    b <-- Tframe _ _ _ [int] (
           Tspec bool [bool] (fun _ -> [bool])
             (fun _ -> True) (fun sl0 b sl1 -> sl1 0 = sl0 0 /\ b = sl0 0));
    Tequiv [bool; int] [int; bool] (sequiv_of_perm (Perm.perm_f_swap #2 0));;
    x <-- Tframe _ _ _ [bool] (Tspec int [int] (fun _ -> [int])
           (fun _ -> True) (fun sl0 x sl1 -> sl1 0 = sl0 0 /\ x = sl0 0));
    Tequiv [int; bool] [bool; int] (sequiv_of_perm (Perm.perm_f_swap #2 0));;
    Tret int (if b then x else 0) (fun _ -> [bool; int])
  )

[@@ __test__]
let test1_shape_tree_ST : ST.shape_tree 2 2 = ST.(
  Sbind _ _ _ (Sframe _ _ 1 (Sspec  1 1))
 (Sbind _ _ _ (Sequiv 2 2 (Veq.mk_veq_eq 2 2 (fun i -> Some (Perm.perm_f_swap #2 0 i))))
 (Sbind _ _ _ (Sframe _ _ 1 (Sspec  1 1))
 (Sbind _ _ _ (Sequiv 2 2 (Veq.mk_veq_eq 2 2 (fun i -> Some (Perm.perm_f_swap #2 0 i))))
              (Sret   true 2)))))


let normal_shape_ST' : list norm_step = [
    delta_only [`%ST.prog_has_shape'; `%ST.bind; `%L.length; `%sequiv_of_perm; `%ST.Mksequiv?.seq_eq];
    delta_qualifier ["unfold"];
    iota; zeta; primops; simplify
  ]

let test1_ST_has_shape () : squash (ST.prog_has_shape' test1_ST test1_shape_tree_ST)
  = _ by T.(norm_test (); norm normal_shape_ST'; trivial ())

[@@ __test__]
let test1_shape_ST : ST.prog_shape test1_ST =
  (**) test1_ST_has_shape ();
  ST.mk_prog_shape test1_ST test1_shape_tree_ST

[@@ __test__]
let test1_SF (b_ini : bool) (x_ini : int) : SF.prog_tree _ _ =
  ST2SF.repr_SF_of_ST test1_ST test1_shape_ST Fl.(cons b_ini (cons x_ini nil))

(*let _ = fun b_ini x_ini ->
  assert (U.print_util (test1_SF b_ini x_ini))
    by T.(clean ();
          norm __normal_ST;
          norm __normal_SF;
          fail "print")*)

[@@ __test__]
let test1_Fun (b_ini : bool) (x_ini : int) = 
  SF2Fun.repr_Fun_of_SF (test1_SF b_ini x_ini)

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
  SF2Fun.repr_Fun_of_SF test2_SF

(*let _ =
  assert (U.print_util test2_Fun)
    by T.(clean ();
          norm __normal_Fun;
          fail "print")*)

//[@@ __test__]
//let test2_wp =
//  Fun.tree_wp test2_Fun (fun x -> b2t x.val_v)

(*#push-options "--print_full_names"
let _ =
  assert (U.print_util test2_wp)
    by T.(clean ();
          norm __normal_Fun;
          norm __normal_Fun_spec;
          fail "print")
#pop-options*)


////////// test3 //////////

[@@ __reduce__; Itf.__repr_M__]
inline_for_extraction
let test3_M (r0 r1 : ref U32.t) : M.repr SH.KSteel unit = MC.(
  x <-- r_read r0;
  r_write r1 U32.(x +%^ 1ul))

[@@ __reduce__]
inline_for_extraction
let test3_mem (r0 r1 : ref U32.t) =
  [vptr' r0 full_perm; vptr' r1 full_perm]

//[@@ handle_smt_goals ]
//let tac () = T.dump "SMT query"

// This generates 2 SMT queries:
// - the WP
// - one for the typing of the requires and ensures clauses
inline_for_extraction
let test3_steel (r0 r1 : ref U32.t)
  : extract unit
      (test3_mem r0 r1) (fun _ -> test3_mem r0 r1)
      (requires fun sl0 -> U32.v (sl0 0) < 42)
      (ensures fun sl0 () sl1 -> U32.v (sl1 1) == U32.v (sl0 0) + 1)
      _ (test3_M r0 r1)
  = _ by (solve_by_wp F.(make_flags_record [Dump Stage_SF]) (timer_start "" true))

(*let _ = fun r0 r1 ->
  assert (U.print_util (test3_steel r0 r1))
    by T.(norm [delta_qualifier ["inline_for_extraction"]];
          fail "print")*)

// This only generates 1 SMT query: the WP
inline_for_extraction
let test3_steel' (r0 r1 : ref U32.t)
  : F.usteel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel #[Extract; Timer(*; O_ST2SF; Dump Stage_ST*)] (
      x <-- call read r0;
      call (write r1) U32.(x +%^ 1ul)
    ) ())

inline_for_extraction
let test3_steel'' (r0 r1 : ref U32.t)
  : F.usteel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel #[Timer; (*; O_ST2SF; Dump Stage_ST*)] (test3_M r0 r1) ())


let test3_steel'_caller (r0 r1 : ref U32.t)
  : Steel U32.t (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == 5ul)
      (ensures fun h0 x h1 -> x == 6ul)
  =
    test3_steel' r0 r1 ();
    read r1


////////// test4 //////////

let test4 (#a : Type) (r : ref a)
  : F.usteel (ref a)
      (vptr r) (fun r' -> vptr r')
      (requires fun h0 -> True)
      (ensures  fun h0 r' h1 -> sel r' h1 == sel r h0)
  = F.(to_steel (return r) ())

////////// test emp //////////

let test_emp_0
  : F.usteel unit
      emp (fun () -> emp)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

let test_emp_1 (#a : Type) (r : ref a)
  : F.usteel unit
      (emp `star` vptr r) (fun () -> vptr r)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

let test_emp_2 (#a : Type) (r : ref a)
  : F.usteel unit
      (vptr r) (fun () -> emp `star` vptr r)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

////////// test frame_equalities //////////

/// The frame equalities are reduced to equalities on the selectors of the vprop'.
/// This relies on the simplification [focus_rmem h q r == h r].
/// However, [Tactics.Effect.rewrite_with_tactic frame_vc_norm] remains in the WP.

let test_frame_equalities_0 (#a : Type) (r0 : ref a)
  : F.usteel unit (vptr r0) (fun () -> vptr r0)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0) h0 h1)
  = F.(to_steel #[Dump Stage_WP] (return ()) ())

let test_frame_equalities_1 (#a : Type) (r0 r1 r2 : ref a)
  : F.usteel unit (vptr r0 `star` vptr r1 `star` vptr r2) (fun () -> vptr r0 `star` vptr r1 `star` vptr r2)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0 `star` vptr r1 `star` vptr r2) h0 h1)
  = F.(to_steel #[Dump Stage_WP] (return ()) ())

let test_steel_with_frame_equality (#a : Type) (r0 r1 : ref a)
  : Steel unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1)
  = Steel.Effect.Atomic.return ()

let test_frame_equalities_2 (#a : Type) (r0 r1 : ref a)
  : F.usteel unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == sel r1 h0) (ensures fun h0 () h1 -> sel r0 h1 == sel r1 h1)
  = F.(to_steel #[Dump Stage_WP] (call (test_steel_with_frame_equality r0) r1) ())

////////// test if-then-else //////////

let test_ite_0 (r : ref U32.t)
  : F.usteel unit (vptr r) (fun () -> vptr r)
      (requires fun _ -> True) (ensures fun _ () h1 -> U32.v (sel r h1) <= 10)
  = F.(to_steel #[Dump Stage_WP]  begin
    x <-- call read r;
    ite U32.(x >=^ 10ul) (
      call (write r) 0ul
    ) (
      call (write r) (U32.(x +%^ 1ul))
    )
  end ())

let test_ite_1 (r : ref U32.t)
  : F.usteel (ref U32.t) (vptr r) (fun r' -> vptr r')
      (requires fun _ -> True) (ensures fun h0 r' h1 -> sel r' h1 == sel r h0)
  = F.(to_steel begin
    ite true (
      return r
    ) (
      return r
    )
  end ())


////////// test pure //////////

// This generates another SMT query that fails
// ? because of a `pure_wp_monotonic`
//[@@ handle_smt_goals ]
//let tac () = T.dump "SMT query"
#push-options "--silent --no_smt"
[@@ expect_failure [298; 298]]
let test_pure0 (x : U32.t)
  : F.usteel unit emp (fun () -> emp)
      (requires fun _ -> U32.v x <= 10) (ensures fun _ () _ -> True)
  = F.(to_steel #[Dump Stage_WP]  begin
    x' <-- pure (fun () -> U32.(x +^ 1ul));
    return ()
  end ())
#pop-options

// There is an SMT query to type-check the program. The condition [UInt.size (UInt32.v x + 1) 32] succeeds
// thanks to the [squash (UInt32.v x <= 10)] introduced by [assert_sq].
let test_pure1 (x : U32.t)
  : F.usteel U32.t emp (fun _ -> emp)
      (requires fun _ -> U32.v x <= 10) (ensures fun _ _ _ -> True)
    by T.(dump "test_pure1")
  = F.(to_steel #[Dump Stage_WP] begin
    _  <-- assert_sq (U32.v x <= 10);
    return U32.(x +^ 1ul)
  end ())


////////// test failures //////////

#push-options "--silent"

[@@ expect_failure [228]]
let test_fail_spec (v : vprop)
  : F.usteel unit v (fun () -> v) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

[@@ expect_failure [228]]
let test_fail_slcond_0 (#a : Type) (r : ref a)
  : F.usteel a emp (fun () -> emp) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (call read r) ())

[@@ expect_failure [228]]
let test_fail_slcond_1 (#a : Type) (r : ref a)
  : F.usteel a (vptr r) (fun () -> emp) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (call read r) ())

[@@ expect_failure [228]]
let test_fail_to_repr_t (#a : Type) (r : ref a) (p : rmem (vptr r) -> prop)
  : F.usteel unit (vptr r) (fun () -> vptr r) (fun h0 -> p h0) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

#pop-options

////////// test ghost //////////

let aux_ghost #opened (r : ref U32.t)
  : SteelGhost int opened (vptr r) (fun _ -> vptr r)
               (requires fun _ -> True) (ensures fun h0 x h1 -> frame_equalities (vptr r) h0 h1 /\ x <= U32.v (sel r h1))
  =
    let x = gget (vptr r) in
    U32.v x

inline_for_extraction
let aux_steel (r : ref U32.t) (x : Ghost.erased int)
  : Steel U32.t (vptr r) (fun _ -> vptr r)
          (requires fun h0 -> x <= U32.v (sel r h0)) (ensures fun h0 x h1 -> frame_equalities (vptr r) h0 h1)
  = read r

inline_for_extraction
let test_ghost0 (r : ref U32.t)
  : F.usteel U32.t (vptr r) (fun _ -> vptr r)
            (requires fun _ -> True) (ensures fun h0 _ h1 -> frame_equalities (vptr r) h0 h1)
  = F.(to_steel #[Extract] (
    x <-- (x <-- call_g aux_ghost r;
     return_g (Ghost.hide x));
    call (aux_steel r) x
  ) ())
// F* reported issues in other files: ["experimental/Steel.Effect.Common.fsti" 460 460 24 37]
// "Unfolding name which is marked as a plugin: frame_vc_norm" 340

let test_ghost1 #opened (r : ghost_ref U32.t)
  : F.usteel_ghost U32.t opened (ghost_vptr r) (fun _ -> ghost_vptr r)
       (requires fun _ -> True) (ensures fun h0 x h1 -> frame_equalities (ghost_vptr r) h0 h1 /\ x == ghost_sel r h0)
  = F.(to_steel_g (
    x  <-- call_g ghost_read r;
    ghost x
  ) ())


////////// test LV //////////

//[@@ handle_smt_goals ]
//let tac () = T.dump "SMT query"

inline_for_extraction
let test3_LV (r0 r1 : ref U32.t)
  : F.usteel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel #[Timer; Extract] (test3_M r0 r1) ())
// time specs     : 86ms
// time lin_cond  : 96ms
// time sub_push  : 30ms
// time LV2SF     : 63ms
// time SF2Fun    : 2ms
// time Fun_wp    : 19ms
// time extract   : 103ms
// total time : 399ms [300ms-500ms]

////////// test GCombinators //////////

inline_for_extraction
let test_slrewrite (r0 r1 r2 : ref U32.t)
  : F.usteel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r2 `star` vptr r1)
      (requires fun _ -> r0 == r2)
      (ensures  fun h0 _ h1 -> sel r0 h0 == sel r2 h1 /\ sel r1 h0 == sel r1 h1)
  = F.(to_steel #[Timer; Extract] (
      GCb.slrewrite r0 r2;;
      return ()
    ) ())
// time specs     : 103ms
// time lin_cond  : 68ms
// time sub_push  : 30ms
// time LV2SF     : 5ms
// time SF2Fun    : 2ms
// time Fun_wp    : 9ms
// time extract   : 58ms
// total time : 275ms

inline_for_extraction
let test_with_invariant_g #opened (r0 : ghost_ref U32.t) (r1 : ref U32.t) (i : inv (ghost_vptr r0))
  : F.usteel_ghost (Ghost.erased U32.t) opened (vptr r1) (fun _ -> vptr r1)
      (requires fun _ -> not (mem_inv opened i)) (ensures fun h0 _ h1 -> frame_equalities (vptr r1) h0 h1)
  = F.(to_steel_g #[Timer; Extract(*; Dump Stage_Extract*)] (
    _ <-- assert_sq (not (mem_inv opened i));
    GCb.with_invariant_g i (
      call_g ghost_read r0
    )) ())
// time specs     : 117ms
// time lin_cond  : 445ms
// time sub_push  : 181ms
// time LV2SF     : 297ms
// time SF2Fun    : 4ms
// time Fun_wp    : 23ms
// time extract   : 776ms
// total time : 1843ms

inline_for_extraction
let test_for_loop_0 (r0 : ref U32.t)
  : F.usteel (U.unit') (vptr r0) (fun _ -> vptr r0)
      (requires fun h0 -> True) (ensures  fun h0 _ h1 -> True)
  = F.(to_steel #[Timer; Extract] (
      GCb.for_loop 0ul 10ul (fun _ -> [vptr' r0 full_perm]) (fun i v -> True)
      begin fun i ->
        elift (return U.Unit')
      end
    ) ())
// time specs     : 38ms
// time lin_cond  : 41ms
// time sub_push  : 6ms
// time LV2SF     : 39ms
// time SF2Fun    : 3ms
// time Fun_wp    : 7ms
// time extract   : 160ms
// total time : 294ms


inline_for_extraction
let test_for_loop_1 (r0 r1 : ref U32.t)
  : F.usteel (U.unit') (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
            (requires fun h0 -> U32.v (sel r0 h0) <= 100)
            (ensures  fun h0 _ h1 -> U32.v (sel r0 h1) = U32.v (sel r0 h0) + 10 /\ sel r1 h1 == sel r1 h0)
  = F.(to_steel #[Timer(*; Extract; Dump Stage_Extract*)] (
      v0 <-- MC.ghost_to_steel (call_g gget (vptr r0));
      GCb.for_loop 0ul 10ul (fun _ -> [vptr' r0 full_perm]) (fun i v -> U32.v (v 0) = U32.v v0 + i)
      begin fun i ->
        _ <-- call read r1;
        x <-- call read r0;
        call (write r0) U32.(x +%^ 1ul);;
        return U.Unit'
      end
    ) ())
// time specs     : 171ms
// time lin_cond  : 932ms
// time sub_push  : 244ms
// time LV2SF     : 3255ms
// time SF2Fun    : 8ms
// time Fun_wp    : 284ms
// total time : 4894ms

// Extract succeeds in ~25s but F* then takes several minutes and a lot of
// memory to finish processing the definition.
// The term resulting from the normalisation is quite big because of the (ghost) tree_cond
// used for the specifications on our Steel combinators.


inline_for_extraction
let test_par0 (r0 r1 : ref U32.t)
  : F.usteel unit (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun _ -> True) (ensures fun _ _ h1 -> sel r0 h1 = 0ul /\ sel r1 h1 = 0ul)
  = F.(to_steel #[Timer; Dump Stage_WP] (
    _ <-- GCb.par (vptr r0) (vptr r1)
      (call (write r0) 0ul)
      (call (write r1) 0ul);
    return ()
  ) ())
// time specs     : 86ms
// time lin_cond  : 870ms
// time sub_push  : 179ms
// time LV2SF     : 6955ms
// time SF2Fun    : 3ms
// time Fun_wp    : 428ms
// total time : 8521ms
