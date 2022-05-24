module Experiment.Steel.CondSolver.Test

module M    = Experiment.Steel.Repr.M
module U    = Learn.Util
module L    = FStar.List.Pure
module Ll   = Learn.List
module Fin  = FStar.Fin
module Perm = Learn.Permutation

open FStar.Tactics
open Learn.Tactics.Util
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
open Experiment.Steel.CondSolver


let _ : elem_index #int 4 [1;3;4;2;7]
  = _ by (build_elem_index dummy_ctx)

[@@ expect_failure [228]]
let _ : elem_index #int 5 [1;3;4;2;7]
  = _ by (build_elem_index dummy_ctx)

[@@ expect_failure [228]]
let _ : elem_index #int 4 L.(0 :: ([1;3] @ [4;2;7]))
  = _ by (build_elem_index dummy_ctx)

unfold
let specT (a : Type) (pre : M.pre_t) (post : M.post_t a) : M.prog_tree a
  = M.Tspec a pre post (fun _ -> True) (fun _ _ _ -> True)

let rec repeat_n (n : nat) (t : M.prog_tree unit) : M.prog_tree unit
  = if n = 0 then M.Tret unit () (fun _ -> [])
    else M.Tbind unit unit t (fun () -> repeat_n (n-1) t)

let norm_test () : Tac unit
  = norm [delta_only [`%repeat_n; `%Ll.initi];
          delta_qualifier ["unfold"];
          iota; zeta; primops]


let test_TCspec_u (v0 v1 : vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _ =
          build (`(M.tree_cond (specT int [(`@v0)] (fun _ -> [(`@v1)]))
                               [(`@v0)] (`#post')))
          (fun () -> norm_test (); build_TCspec false false)
        in ())

let test_TCspec_p (v0 v1 v2 : vprop') (vx : int -> vprop')
  : M.tree_cond (specT int [v0; v1] (fun x -> [v0; vx x]))
                ([v0; v1; v2]) (fun x -> [v2; vx x; v0])
  = _ by (norm_test (); let _ = build_TCspec false true in ())


let test_TCspecS_u (v0 v1 : vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _ =
          build (`(M.tree_cond (M.TspecS int (VUnit (`@v0)) (fun _ -> VUnit (`@v1)) (fun _ -> True) (fun _ _ _ -> True))
                               [(`@v0)] (`#post')))
          (fun () -> norm_test (); build_TCspec true false)
        in ())

let test_TCspecS_p (v0 v1 v2 : vprop') (vx : int -> vprop')
  : M.tree_cond (M.TspecS int (VUnit v0 `star` VUnit v1) (fun x -> VUnit v0 `star` VUnit (vx x))
                            (fun _ -> True) (fun _ _ _ -> True))
                ([v0; v1; v2]) (fun x -> [v2; vx x; v0])
  = _ by (norm_test (); let _ = build_TCspec true true in ())


let test_TCret_u (v0 v1 : vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,_ =
          build (`(M.tree_cond (M.Tret int 42 (fun _ -> [])) [(`@v0); (`@v1)] (`#post')))
          (fun () -> build_TCret false)
        in ())

let test_TCret_p (v0 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond (M.Tret int 42 (fun _ -> []))
                ([v0; vx0 42; vx1 42]) (fun x -> [v0; vx1 x; vx0 42])
  = _ by (let _ = build_TCret true in ())


let test_TCbind_u (v0 v1 : vprop') (vx0 : int -> vprop') : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,() =
          build (`(M.tree_cond
            (M.Tbind int int (specT int []          (fun x -> [(`@vx0) x]))
                   (fun x -> specT int [(`@vx0) x] (fun _ -> [(`@v1)])))
            [(`@v0)] (`#post')))
          (fun () ->
            norm_test ();
            apply (`M.TCbind);
            let _ = build_TCspec false false in
            let x = intro () in
            norm_cond_sol ();
            let post1 = fresh_uvar None in
            apply_raw (`(__defer_post_unification (`#post1)));
            let _ = build_TCspec false false in
            norm_cond_sol (); trefl ()
          )
        in ())

let test_TCbind_p (v0 v1 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int (specT int []      (fun x -> [vx0 x])    )
               (fun x -> specT int [vx0 x] (fun y -> [v1; vx1 y])))
            [v0] (fun y -> [v0; vx1 y; v1])
  = _ by (
    norm_test ();
    apply (`M.TCbind);
    let _ = build_TCspec false false in
    let x = intro () in
    norm_cond_sol ();
    let _ = build_TCspec false true in
    ()
  )


let test_TCbindP_u (v0 v1 : vprop') (vx0 : int -> vprop') (wp : pure_wp int) (f : unit -> PURE int wp) : squash True =
  _ by (let post' = fresh_uvar (Some (`(M.post_t int))) in
        let _,() =
          build (`(M.tree_cond
            (M.TbindP int int (`@wp) (`@f)
                    (fun x -> specT int [(`@v0)] (fun y -> [(`@vx0) y])))
            [(`@v0); (`@v1)] (`#post')))
          (fun () ->
            norm_test ();
            apply (`M.TCbindP);
            let x = intro () in
            let post1 = fresh_uvar None in
            apply_raw (`(__defer_post_unification (`#post1)));
            let _ = build_TCspec false false in
            norm_cond_sol (); trefl ()
          )
        in ())

let test_TCbindP_p (v0 v1 : vprop') (vx0 : int -> vprop') (wp : pure_wp int) (f : unit -> PURE int wp)
  : M.tree_cond
        (M.TbindP int int wp f
                (fun x -> specT int [v0] (fun y -> [vx0 y])))
            [v0; v1] (fun y -> [v1; vx0 y])
  = _ by (
    norm_test ();
    apply (`M.TCbindP);
    let x = intro () in
    let _ = build_TCspec false true in ()
  )


let test_build_tree_cond_0 (v0 v1 : vprop') (vx0 vx1 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int (specT int []      (fun x -> [vx0 x]))
               (fun x -> specT int [vx0 x] (fun y -> [v1; vx1 y])))
            [v0] (fun y -> [v0; vx1 y; v1])
  = _ by (norm_test (); let shp = build_tree_cond true in _)

let test_build_prog_cond_0 (v0 v1 : vprop') (vx0 vx1 : int -> vprop')
  : M.prog_cond
        (M.Tbind int int (specT int []      (fun x -> [vx0 x]))
               (fun x -> specT int [vx0 x] (fun y -> [v1; vx1 y])))
        [v0] (fun y -> [v0; vx1 y; v1])
  = _ by (norm_test (); build_prog_cond ())

let _ = fun v0 v1 vx0 vx1 ->
  assert (U.print_util (test_build_prog_cond_0 v0 v1 vx0 vx1))
      by (norm [delta_only [`%test_build_prog_cond_0]; delta_attr [`%__tac_helper__]];
          dump "print")

(*let test_build_prog_cond_1 (v : int -> vprop')
  : M.prog_cond
        (repeat_n 100 (specT unit (Ll.initi 0 2 v) (fun () -> Ll.initi 0 2 (fun i -> v (1 - i)))))
        (Ll.initi 0 5 v) (fun () -> Ll.initi 0 5 v)
  = _ by (norm_test ();
          let t = timer_start "buil_prog_cond" in
          build_prog_cond ();
          timer_stop t)*)


/// This example fails because the resolution of the innermost [M.Tret] has to infer its post. In this case the
/// inferred post is simply the current vprops, ignoring the returned value (i.e. [fun _ -> pre] in [__build_TCret_u]).
/// But at this point pre is [vx0 x] where [x] is bound, the inferred post is thus [fun _ -> [vx0 x]] which
/// depends on [x].
[@@expect_failure [228]]
let test_build_tree_cond__Tret_u_0 (vx0 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int
            (M.Tbind int int (specT int [] (fun x -> [vx0 x])) (fun x -> M.Tret int x (fun _ -> [])))
            (fun x -> M.Tret int x (fun _ -> [])))
        [] (fun x -> [vx0 x])
  = _ by (norm_test (); let _ = build_tree_cond true in ())

/// This example works because the resolution of [M.Tret] is given the expected post (the post of the whole
/// program), [fun x' -> [vx0 x']].
let test_build_tree_cond__Tret_u_1 (vx0 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int (specT int [] (fun x -> [vx0 x])) (fun x -> M.Tret int x (fun _ -> [])))
        [] (fun x -> [vx0 x])
  = _ by (norm_test (); let _ = build_tree_cond true in ())

/// This example works because we annotate the innermost [M.Tret] with an hint.
let test_build_tree_cond__Tret_u_2 (v0 : vprop') (vx0 : int -> vprop')
  : M.tree_cond
        (M.Tbind int int
            (M.Tbind int int (specT int [] (fun x -> [v0; vx0 x])) (fun x -> M.Tret int x (fun x' -> [vx0 x'])))
            (fun x -> M.Tret int x (fun _ -> [])))
        [] (fun x -> [v0; vx0 x])
  = _ by (norm_test (); let _ = build_tree_cond true in ())


/// This example fails because we cannot find a [v0] in the pre.
[@@expect_failure [228]]
let test_build_tree_cond__not_found (v0 : vprop')
  : M.tree_cond
        (specT int [v0] (fun _ -> []))
        [] (fun _ -> [])
  = _ by (norm_test (); let _ = build_tree_cond true in ())

/// This example fails because we obtain [fun _ -> [v0]] as post which is not unifiable with the expected post
/// [fun _ -> []]
[@@expect_failure [228]]
let test_build_tree_cond__post (v0 : vprop')
  : M.tree_cond
        (specT int [] (fun _ -> [v0]))
        [] (fun _ -> [])
  = _ by (norm_test (); let _ = build_tree_cond true in ())


[@@expect_failure]
let test_steel__ret_ghost_0 (r : ref int)
  : SteelT (Ghost.erased (ref int)) (vptr r) (fun r' -> vptr (Ghost.reveal r'))
  = Steel.Effect.Atomic.return (Ghost.hide r)

let test_steel__ret_ghost_1 (r : ref int)
  : SteelT (Ghost.erased (ref int)) (vptr r) (fun r' -> vptr (Ghost.reveal r'))
  = let r' = Ghost.hide r in
    Steel.Effect.Atomic.return r'

[@@expect_failure]
let test_steel__ret_f (v : int -> vprop) (x : int) (f : int -> int)
  : SteelT int (v (f x)) (fun y -> v y)
  = Steel.Effect.Atomic.return (f x)

(* TODO : mark vprop' as erasable
let test_build_tree_cond__ret_ghost (r : ref int)
  : M.tree_cond
        (M.Tret (Ghost.erased (ref int)) (Ghost.hide r) (fun _ -> []))
        [vptr' r full_perm] (fun r' -> [vptr' (Ghost.reveal r') full_perm])
   = _ by (norm_test (); let _ = build_tree_cond true in ())*)

let test_build_tree_cond__ret_f (v : int -> vprop') (x : int) (f : int -> int)
  : M.tree_cond
        (M.Tret int (f x) (fun _ -> []))
        [v (f x)] (fun y -> [v y])
   = _ by (norm_test (); let _ = build_tree_cond true in ())
