module Experiment.Steel.Effect.Test

open FStar.Tactics
open Steel.Effect.Common
open Steel.Reference
open Experiment.Steel.Interface
open Experiment.Steel.Effect

let display_term (#a : Type) (x : a) : Type = unit

/// This retypecheck [r]. It fails if r contains a bind_pure since it will need to prove the monotonicity of the
/// weakest precondition ([pure_wp_monotonic]).
let dump_repr (#a : Type) (#r : prog_tree a)
      ($re : unit -> MRepr a r)
      (#[(norm [delta_attr [`%__repr_M__]; iota]; dump "dump_repr"; exact (`()))] d : display_term r)
      ()
  : unit
  = ()


let test0 =
  dump_repr (fun () -> let x = return 5 in return (x + 1)) ()

//[@@ handle_smt_goals ] let tac () = Tactics.dump "SMT query"
[@@ expect_failure [19]]
let test1 = dump_repr (fun () -> assert (5 >= 0); return 5) ()

let test1' (x : int)
  : usteel int emp (fun _ -> emp) (requires fun _ -> x >= 1) (ensures fun _ y _ -> y >= 5)
  = to_steel #[Dump Stage_WP] begin fun () ->
    assert (x >= 0);
    return (5 + x)
  end
  

//let test2 (r : ref int) =
//  dump_repr (fun () -> let x = call read r in return x) ()

// Stack overflow
//let test3 (b : bool) (r0 r1 : ref int) =
//  dump_repr (fun () -> if b then let x = read r0 in return x
//                         else let x = read r1 in return x)

let test3' (b : bool) (r0 r1 : ref int)
  : usteel int (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
         (requires fun h0 -> sel r0 h0 >= 0 /\ sel r1 h0 >= 0)
         (ensures  fun h0 x h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1 /\ x >= 0)
  = to_steel #[Timer] begin fun () ->
    if b then call read r0 else call read r1
  end

//let test4 (r0 r1 : ref int) =
//  dump_repr (fun () ->
//    let x = call read r0 in
//    call (write r1) (x + 1);
//    return ())
//  ()

// With the sub_effect Steel ~> MRepr, fails because the prog_tree contains some uvar
// (because the Steel's tactic is called after our tactic ?)
//[@@ expect_failure [228]]
//let test5 (r : ref nat)
//  : usteel unit
//      (vptr r) (fun _ -> vptr r)
//      (requires fun h0 -> sel r h0 > 10) (ensures fun _ _ h1 -> sel r h1 >= 10)
//  = to_steel #[Dump Stage_M] begin fun () ->
//    let x = read r in
//    let _ = return () in
//    write r (x - 1);
//    return ()
//  end

let test5' (r : ref nat)
  : usteel unit
      (vptr r) (fun _ -> vptr r)
      (requires fun h0 -> sel r h0 > 10) (ensures fun _ _ h1 -> sel r h1 >= 10)
  = to_steel begin fun () ->
    let x = call read r in
    call (write r) (x - 1)
  end
