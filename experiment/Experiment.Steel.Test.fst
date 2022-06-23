module Experiment.Steel.Test

module U    = Learn.Util
module T    = FStar.Tactics
module L    = FStar.List.Pure
module Ll   = Learn.List
module Dl   = Learn.DList
module Fl   = Learn.FList
module SU   = Learn.Steel.Util
module U32  = FStar.UInt32
module Perm = Learn.Permutation

module F      = Experiment.Steel.Notations
module M      = Experiment.Steel.Repr.M
module MC     = Experiment.Steel.Combinators
module ST     = Experiment.Steel.Repr.ST
module LV     = Experiment.Steel.Repr.LV
module SF     = Experiment.Steel.Repr.SF
module SH     = Experiment.Steel.Steel
module Fun    = Experiment.Repr.Fun
module Vpl    = Experiment.Steel.VPropList
module Veq    = Experiment.Steel.VEquiv
module M2ST   = Experiment.Steel.Repr.M_to_ST
module ST2SF  = Experiment.Steel.Repr.ST_to_SF.Spec
module SF2Fun = Experiment.Steel.Repr.SF_to_Fun

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
let read_pre  #a (r : ref a) : M.pre_t
  = [vptr' r full_perm]
unfold
let read_post #a (r : ref a) : M.post_t a
  = fun _ -> [vptr' r full_perm]
unfold
let read_req  #a (r : ref a) : M.req_t (read_pre r)
  = fun sl0 -> True
unfold
let read_ens  #a (r : ref a) : M.ens_t (read_pre r) a (read_post r)
  = fun sl0 x sl1 ->
    sl0 0 == sl1 0 /\ x == sl1 0

inline_for_extraction
let steel_read #a (r : ref a) () :
  Steel a (Vpl.vprop_of_list [vptr' r full_perm]) (fun _ -> Vpl.vprop_of_list [vptr' r full_perm])
    (requires fun _ -> True)
    (ensures fun h0 x h1 -> let sl0 = Vpl.sel_f [vptr' r full_perm] h0 in
                         let sl1 = Vpl.sel_f [vptr' r full_perm] h1 in
                         sl0 0 == sl1 0 /\ x == sl1 0)
  =
    (**) change_equal_slprop (Vpl.vprop_of_list [vptr' r full_perm]) (vptr r `star` emp);
    let x = read r in
    (**) change_equal_slprop (vptr r `star` emp) (Vpl.vprop_of_list [vptr' r full_perm]);
    Steel.Effect.Atomic.return x

[@@ __test__; __reduce__]
inline_for_extraction
let r_read (#a : Type0) (r : ref a) : M.repr SH.KSteel a =
  MC.repr_of_steel_r (read_pre r) (read_post r) (read_req r) (read_ens r) (SH.steel_f (steel_read r))

inline_for_extraction
let steel_write #a (r : ref a) (x : a) ()
  : Steel unit (Vpl.vprop_of_list [vptr' r full_perm]) (fun _ -> Vpl.vprop_of_list [vptr' r full_perm])
               (requires fun _ -> True) (ensures fun h0 () h1 -> x == Vpl.sel_f [vptr' r full_perm] h1 0)
  =
    (**) change_equal_slprop (Vpl.vprop_of_list [vptr' r full_perm]) (vptr r `star` emp);
    write r x;
    (**) change_equal_slprop (vptr r `star` emp) (Vpl.vprop_of_list [vptr' r full_perm])

[@@ __test__; __reduce__]
inline_for_extraction
let r_write #a (r : ref a) (x : a) : M.repr SH.KSteel unit =
  MC.repr_of_steel_r [vptr' r full_perm] (fun _ -> [vptr' r full_perm])
                    (fun sl0 -> True) (fun sl0 () sl1 -> x == sl1 0)
                    (SH.steel_f (steel_write r x))

[@@ __test__; __reduce__]
let test0_M (r : ref nat) : M.repr SH.KSteel nat = MC.(
  x <-- r_read r;
  return x)

let normal_vp : list norm_step = [
    delta_only [`%L.map; `%L.append; `%L.op_At];
    delta_qualifier ["unfold"];
    delta_attr [`%__tac_helper__];
    iota; zeta_full
  ]

(*let _ = fun r ->
  assert (U.print_util (test0_M r).repr_tree) by T.(norm __normal_M; qed ())*)

unfold
let test0_equiv (r : ref nat) (v : vprop') : Veq.vequiv ([vptr' r full_perm; v]) [vptr' r full_perm; v] =
  Veq.vequiv_of_perm (Perm.id_n 2)

[@@ __test__]
let test0_cond (r : ref nat) (v : vprop')
  : M.tree_cond (test0_M r).repr_tree [vptr' r full_perm; v] (fun _ -> [vptr' r full_perm; v])
  = _ by T.(
    norm __normal_M;
    apply (`M.TCbind);
     (let u_s  = fresh_uvar None in
      let u_p0 = fresh_uvar None in
      let u_p1 = fresh_uvar None in
      apply (`(M.TCspec #nat #(M.spec_r_exact (`#u_s)) (`#u_s) M.SpecExact (M.Mktree_cond_Spec
          [vptr' (`@r) full_perm; (`@v)] (fun _ -> [vptr' (`@r) full_perm; (`@v)]) [(`@v)] (`#u_p0) (`#u_p1))));
       (unshelve u_p0; norm normal_vp; exact (`test0_equiv (`@r) (`@v)));
       (unshelve u_p1;
        let x = intro () in
        norm normal_vp;
        exact (`test0_equiv (`@r) (`@v))));
     (let x = intro () in
      apply (`M.TCret);
       (norm normal_vp; exact (`test0_equiv (`@r) (`@v))));
  qed ())

unfold
let test0_equiv_l : Veq.veq_eq_t_list 2 2 = [Some 0; Some 1]

[@@ __test__]
let test0_shape_M : M.shape_tree 2 2 = M.(
  Sbind _ _ _ (Sspec 1 1 2 2 1 test0_equiv_l test0_equiv_l)
              (Sret 2 2 test0_equiv_l))

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
  ST.flatten_prog (M2ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r v))

(*let _ = fun r ->
   assert (U.print_util (test0_ST r (to_vprop' Steel.Memory.emp)))
       by T.(norm_test ();
             norm __normal_ST;
             fail "print")*)

[@@ __test__]
let test0_shape_ST (r : ref nat) (v : vprop') : ST.prog_shape (test0_ST r v)
  = 
    (**) test0_M_has_shape r v;
    (**) M2ST.repr_ST_of_M_shape (test0_M r).repr_tree (test0_cond r v) test0_shape_M;
    let s = M2ST.shape_ST_of_M test0_shape_M in
    (**) ST.flatten_prog_shape (M2ST.repr_ST_of_M (test0_M r).repr_tree (test0_cond r v)) s;
    ST.mk_prog_shape (test0_ST r v) (ST.flatten_shape s)

(*let _ = fun r v ->
   assert (U.print_util (test0_shape_ST r v))
       by T.(norm_test (); norm __normal_ST; fail "print")*)

[@@ __test__]
let test0_SF (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) : SF.prog_tree _ _ =
  ST2SF.repr_SF_of_ST (test0_ST r v) (test0_shape_ST r v) Fl.(cons x_ini (cons v_ini nil))

(*let _ = fun r (p : Steel.Memory.slprop) x_ini ->
    assert (U.print_util (test0_SF r (to_vprop' p) x_ini ()))
        by T.(clean ();
              norm __normal_ST;
              norm __normal_SF;
              fail "print")*)

[@@ __test__]
let test0_shape_SF (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) : SF.prog_shape (test0_SF r v x_ini v_ini)
  =
    (**) ST2SF.repr_SF_of_ST_shape (test0_ST r v) (test0_shape_ST r v) Fl.(cons x_ini (cons v_ini nil));
    SF.mk_prog_shape (test0_SF r v x_ini v_ini) (ST2SF.shape_SF_of_ST (test0_shape_ST r v).shp)

(*let _ = fun r v x_ini v_ini ->
  assert (U.print_util (test0_shape_SF r v x_ini v_ini))
    by T.(clean ();
          norm __normal_ST;
          norm __normal_SF;
          fail "print")*)


[@@ __test__]
let test0_Fun (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) = 
  SF2Fun.repr_Fun_of_SF (test0_SF r v x_ini v_ini)

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


(* This makes the extraction fail (even with noextract)
unfold noextract
let test0_wp (r : ref nat) (v : vprop') (x_ini : nat) (v_ini : v.t) =
  Fun.tree_wp (test0_Fun r v x_ini v_ini) (fun res -> res.val_v >= 0)*)

(*let _ = fun r p x_ini ->
    assert (U.print_util (test0_wp r (to_vprop' p) x_ini ()))
        by T.(clean ();
              norm __normal_ST;
              norm __normal_SF;
              norm __normal_Fun;
              norm __normal_Fun_spec;
              fail "print")*)


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

[@@ __reduce__]
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
      (test3_M r0 r1)
  = _ by (solve_by_wp F.default_flags (timer_start "" true))

(*let _ = fun r0 r1 ->
  assert (U.print_util (test3_steel r0 r1))
    by T.(norm [delta_qualifier ["inline_for_extraction"]];
          fail "print")*)



// The SMT query still contains some references to test3_mem, Vpl.vprop_list_sels_t...
// and an application of Dl.initi_g that is not reduced
#push-options "--ifuel 0"
let test3_steel_caller (r0 r1 : ref U32.t)
  : Steel U32.t (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == 5ul)
      (ensures fun h0 x h1 -> x == 6ul)
  =
    call_repr_steel (test3_steel r0 r1);
    read r1
#pop-options

// This only generates 1 SMT query: the WP
// FIXME: the use of call make ST -> SF and SF -> Fun longer when using O_ST2SF
//        even if the dump at stage ST are (nearly) identical
inline_for_extraction
let test3_steel' (r0 r1 : ref U32.t)
  : F.steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel (
      x <-- call read r0;
      call (write r1) U32.(x +%^ 1ul)
    ) #(_ by (mk_steel [Extract; Timer(*; O_ST2SF; Dump Stage_ST*)])) ())

inline_for_extraction
let test3_steel'' (r0 r1 : ref U32.t)
  : F.steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel (test3_M r0 r1) #(_ by (mk_steel [Timer(*; O_ST2SF; Dump Stage_ST*)])) ())


let test3_steel'_caller (r0 r1 : ref U32.t)
  : Steel U32.t (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == 5ul)
      (ensures fun h0 x h1 -> x == 6ul)
  =
    test3_steel' r0 r1 ();
    read r1


////////// test4 //////////

let test4 (#a : Type) (r : ref a)
  : F.steel (ref a)
      (vptr r) (fun r' -> vptr r')
      (requires fun h0 -> True)
      (ensures  fun h0 r' h1 -> sel r' h1 == sel r h0)
  = F.(to_steel (return r) ())

////////// test emp //////////

let test_emp_0
  : F.steel unit
      emp (fun () -> emp)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

let test_emp_1 (#a : Type) (r : ref a)
  : F.steel unit
      (emp `star` vptr r) (fun () -> vptr r)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

let test_emp_2 (#a : Type) (r : ref a)
  : F.steel unit
      (vptr r) (fun () -> emp `star` vptr r)
      (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

////////// test frame_equalities //////////

/// The frame equalities are reduced to equalities on the selectors of the vprop'.
/// This relies on the simplification [focus_rmem h q r == h r].
/// However, [Tactics.Effect.rewrite_with_tactic frame_vc_norm] remains in the WP.

let test_frame_equalities_0 (#a : Type) (r0 : ref a)
  : F.steel unit (vptr r0) (fun () -> vptr r0)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0) h0 h1)
  = F.(to_steel (return ()) #(_ by (mk_steel [Dump Stage_WP])) ())

let test_frame_equalities_1 (#a : Type) (r0 r1 r2 : ref a)
  : F.steel unit (vptr r0 `star` vptr r1 `star` vptr r2) (fun () -> vptr r0 `star` vptr r1 `star` vptr r2)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0 `star` vptr r1 `star` vptr r2) h0 h1)
  = F.(to_steel (return ()) #(_ by (mk_steel [Dump Stage_WP])) ())

let test_steel_with_frame_equality (#a : Type) (r0 r1 : ref a)
  : Steel unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1)
  = Steel.Effect.Atomic.return ()

let test_frame_equalities_2 (#a : Type) (r0 r1 : ref a)
  : F.steel unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
      (requires fun h0 -> sel r0 h0 == sel r1 h0) (ensures fun h0 () h1 -> sel r0 h1 == sel r1 h1)
  = F.(to_steel (call (test_steel_with_frame_equality r0) r1) #(_ by (mk_steel [Dump Stage_WP])) ())

////////// test if-then-else //////////

let test_ite_0 (r : ref U32.t)
  : F.steel unit (vptr r) (fun () -> vptr r)
      (requires fun _ -> True) (ensures fun _ () h1 -> U32.v (sel r h1) <= 10)
  = F.(to_steel begin
    x <-- call read r;
    ite U32.(x >=^ 10ul) (
      call (write r) 0ul
    ) (
      call (write r) (U32.(x +%^ 1ul))
    )
  end #(_ by (mk_steel [Dump Stage_WP])) ())

let test_ite_1 (r : ref U32.t)
  : F.steel (ref U32.t) (vptr r) (fun r' -> vptr r')
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
#push-options "--silent"
[@@ expect_failure [19]]
let test_pure (x : U32.t)
  : F.steel unit emp (fun () -> emp)
      (requires fun _ -> U32.v x <= 10) (ensures fun _ () _ -> True)
  = F.(to_steel begin
    x' <-- pure (fun () -> U32.(x +^ 1ul));
    return ()
  end #(_ by (mk_steel [Dump Stage_WP])) ())
#pop-options

////////// test failures //////////

#push-options "--silent"

[@@ expect_failure [228]]
let test_fail_spec (v : vprop)
  : F.steel unit v (fun () -> v) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

[@@ expect_failure [228]]
let test_fail_slcond_0 (#a : Type) (r : ref a)
  : F.steel a emp (fun () -> emp) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (call read r) ())

[@@ expect_failure [228]]
let test_fail_slcond_1 (#a : Type) (r : ref a)
  : F.steel a (vptr r) (fun () -> emp) (fun _ -> True) (fun _ _ _ -> True)
  = F.(to_steel (call read r) ())

[@@ expect_failure [228]]
let test_fail_to_repr_t (#a : Type) (r : ref a) (p : rmem (vptr r) -> prop)
  : F.steel unit (vptr r) (fun () -> vptr r) (fun h0 -> p h0) (fun _ _ _ -> True)
  = F.(to_steel (return ()) ())

#pop-options

////////// test time //////////

let steel_id (#a : Type) (r : ref a)
  : Steel unit (vptr r) (fun () -> vptr r)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r) h0 h1)
  = Steel.Effect.Atomic.return ()

[@@ __reduce__]
let rec repeat_n (n : nat) (t : M.repr SH.KSteel unit) : M.repr SH.KSteel unit
  = F.(if n = 0 then return () else (t;; repeat_n (n-1) t))

(*let test_time (#a : Type) (r : ref a)
  : F.steel unit (vptr r) (fun () -> vptr r)
      (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r) h0 h1)
  = F.(to_steel (repeat_n 30 (call steel_id r))
        #(_ by (T.norm [delta_only [
                         `%Vpl.vprop_list_sels_t;   `%M.Mkrepr?.repr_tree;
                         `%M.Mkprog_cond?.pc_tree;  `%M.Mkprog_cond?.pc_post_len; `%M.Mkprog_cond?.pc_shape;
                         `%L.map; `%Mkvprop'?.t;
                         `%prog_M_to_Fun];
                      delta_attr [`%__tac_helper__; `%M.__repr_M__; `%__steel_reduce__; `%__reduce__];
                      delta_qualifier ["unfold"];
                      iota; zeta; primops];
               mk_steel [Timer; Extract]))
         ())*)

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
let test_ghost (r : ref U32.t)
  : F.steel U32.t (vptr r) (fun _ -> vptr r)
            (requires fun _ -> True) (ensures fun h0 _ h1 -> frame_equalities (vptr r) h0 h1)
  = F.(to_steel (
    x <-- MC.ghost_to_steel (MC.bind_ghost (call_g aux_ghost r) (fun x ->
                                         MC.return_ghost (Ghost.hide x)));
    call (aux_steel r) x
  ) #(_ by (mk_steel [Extract])) ())

////////// test vprop_group //////////

#push-options "--silent"
[@@ expect_failure [228]]
let test_id_fail (v : vprop)
  : F.steel unit v (fun () -> v)
       (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities v h0 h1)
  = F.(to_steel (return ()) ())
#pop-options

let test_id_ok (v : vprop')
  : F.steel unit (VUnit v) (fun () -> VUnit v)
       (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (VUnit v) h0 h1)
  = F.(to_steel (return ()) ())

// TODO: improve the WP
let test_id_caller (r0 r1 : ref U32.t)
  : F.steel unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
       (requires fun _ -> True) (ensures fun h0 () h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1)
  = F.(to_steel (
    call (test_id_ok (SU.vprop_group' (Vpl.vprop_of_list [vptr' r0 full_perm; vptr' r1 full_perm]))) ()
    ) #(_ by (mk_steel [Timer; Dump Stage_WP])) ())

////////// test smt_fallback //////////

let test_smt_fallback (r0 r1 : ref U32.t)
  : F.steel unit (vptr r0) (fun () -> vptr r1)
        (requires fun _ -> r0 == r1) (ensures fun h0 () h1 -> sel r0 h0 = sel r1 h1)
  = F.(to_steel (
    return ()
    ) #(_ by (mk_steel [Dump Stage_WP])) ())

////////// test LV //////////

//[@@ handle_smt_goals ]
//let tac () = T.dump "SMT query"

inline_for_extraction
let test3_LV (r0 r1 : ref U32.t)
  : F.steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel (test3_M r0 r1) #(_ by (mk_steel [O_LV; Timer; Extract])) ())
// time specs     : 54ms
// time lin_cond  : 42ms
// time sub_push  : 29ms
// time LV2SF     : 59ms
// time SF2Fun    : 3ms
// time Fun_wp    : 18ms
// time extract   : 39ms
// total time : 244ms

inline_for_extraction
let test3_LV' (r0 r1 : ref U32.t)
  : F.steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = F.(to_steel (
      x <-- call read r0;
      call (write r1) U32.(x +%^ 1ul)
    ) #(_ by (mk_steel [O_LV; Timer; Extract])) ())
// time specs     : 87ms
// time lin_cond  : 177ms
// time sub_push  : 50ms
// time LV2SF     : 83ms
// time SF2Fun    : 5ms
// time Fun_wp    : 24ms
// time extract   : 64ms
// total time : 490ms
