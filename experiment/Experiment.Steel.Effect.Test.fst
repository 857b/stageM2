module Experiment.Steel.Effect.Test

module M   = Experiment.Steel.Repr.M
module SH  = Experiment.Steel.Steel
module Mem = Steel.Memory
module U32 = FStar.UInt32

open FStar.Tactics
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference
open Experiment.Steel.Interface
open Experiment.Steel.Effect


let display_term (#a : Type) (x : a) : Type = unit

/// This retypecheck [r]. It fails if r contains a bind_pure since it will need to prove the monotonicity of the
/// weakest precondition ([pure_wp_monotonic]).
let dump_repr (#a : Type) (#r : prog_tree a) (ek : SH.effect_kind) (#loc : location_p)
      ($re : unit -> MRepr a ek r None loc)
      (#[(norm [delta_attr [`%__repr_M__]; iota]; dump "dump_repr"; exact (`()))] d : display_term r)
      ()
  : unit
  = ()

// We need to annotate [SH.KGhostI Set.empty] otherwise the infered effect is [SH.KGhostI ?opened] and
// ?opened is not constrained
let test0 =
  dump_repr (SH.KGhostI Set.empty) (fun () -> let x = return 5 in return (x + 1)) ()

#push-options "--no_smt"
[@@ expect_failure [298]]
let test1 = dump_repr (SH.KGhostI Set.empty) (fun () -> assert (5 >= 0); return 5) ()
#pop-options


let test1' (x : int)
  : usteel int emp (fun _ -> emp) (requires fun _ -> x >= 1) (ensures fun _ y _ -> y >= 5)
  = to_steel #[Dump Stage_WP] begin fun () ->
    assert (x >= 0);
    return (5 + x)
  end

// This conversion is needed to avoid the unnecessary bind_pure that appears when using [call]
let mread  #a   = convert_steel (read  #a)
let mwrite #a r = convert_steel (write #a r)

// Stack overflow
//let test2 (r : ref int) =
//  dump_repr SH.KSteel (fun () -> let x = call read r in return x) ()

//let test3 (b : bool) (r0 r1 : ref int) =
//  dump_repr (fun () -> if b then let x = read r0 in return x
//                         else let x = read r1 in return x)

//[@@ handle_smt_goals ] let tac () = Tactics.dump "SMT query"

// There is no side conditions due to retyping
// The WP is the only SMT query
let test3' (b : bool) (r0 r1 : ref int)
  : usteel int (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
         (requires fun h0 -> sel r0 h0 >= 0 /\ sel r1 h0 >= 0)
         (ensures  fun h0 x h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1 /\ x >= 0)
  = to_steel #[Dump Side_Conditions; Dump Stage_WP] begin fun () ->
    if b then mread r0 else mread r1
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

let __assert_sq (#opened : Mem.inames) (p : Type)
  : SteelGhost (squash p) opened emp (fun _ -> emp) (requires fun _ -> p) (ensures fun _ _ _ -> True)
  = noop ()

let assert_sq #opened = convert_steel_ghost (__assert_sq #opened)

// Without the call to [assert_sq], this fails when rechecking the specification of write.
// Indeed we [x - 1 >= 0] for this check to succeed.
// F* already introduces a bind pure that assert this fact with the WP:
//   [fun p -> x - 1 >= 0 /\ (forall (return_val : nat) . return_val == x - 1 ==> p return_val)]
// However, the [x  - 1] is not replaced by [return_val] in the tree.
// Since we do not allow the well-typing of the program tree to depend on its requirement, the program is
// indeed ill-typed.
// By calling [assert_sq], we explicitly introduce a variable with type [squash (x - 1 >= 0)] our tree can depends on.

let test5' (r : ref nat)
  : usteel unit
      (vptr r) (fun _ -> vptr r)
      (requires fun h0 -> sel r h0 > 10) (ensures fun _ _ h1 -> sel r h1 >= 10)
  = to_steel #[Dump Stage_M] begin fun () ->
    let x = mread r in
    let _ = assert_sq (x - 1 >= 0) in
    mwrite r (x - 1)
  end

let mghost_read  #a #opened   = convert_steel_ghost (ghost_read  #a #opened)
let mghost_write #a #opened r = convert_steel_ghost (ghost_write #a #opened r)

let test6 (opened : Mem.inames) (r : ghost_ref int) (x : int)
  : usteel_ghost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    mghost_write r x;
    mghost_write r x
  end

// Since MReprGhost is erasable, we can use ghost operations
let test7 (opened: Mem.inames) (r : ghost_ref int)
  : usteel_ghost int opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    let x = mghost_read r in
    Ghost.reveal x
  end

let test8 (opened : Mem.inames) (r : ghost_ref int) (b : bool) (x0 x1 : int)
  : usteel_ghost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    if b
    then mghost_write r x0
    else mghost_write r x1
  end

let test9 (r : ghost_ref int) (x : int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    mghost_write r x
  end

let test9' (r : ghost_ref int) (x : int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    mghost_write r x;
    return ()
  end

let test10 (r0 r1 : ref U32.t)
  : usteel unit (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel r0 h1 = sel r1 h0 /\ sel r1 h1 = sel r0 h0)
  = to_steel begin fun () ->
    // note: using match blocks some reductions
    //let () = () in
    let x0 = mread r0 in
    let x1 = mread r1 in
    mwrite r0 x1;
    mwrite r1 x0
  end

[@@ expect_failure]
let test11 #opened (r : ref int)
  : usteel_ghost unit opened (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    mwrite r 0
  end

[@@ expect_failure]
let test12 (r : ghost_ref int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    let x = mghost_read r in
    Ghost.reveal x
  end

let atomic_write_u32 #opened (r : ref U32.t) (x : U32.t)
  : SteelAtomic unit opened
      (vptr r) (fun _ -> vptr r)
      (requires fun _ -> True) (ensures fun _ _ h1 -> sel r h1 = x)
  =
    let x0 = elim_vptr r _ in
    atomic_write_pt_u32 r x;
    intro_vptr r _ x

let matomic_write_u32 #opened r = convert_steel_atomic (atomic_write_u32 #opened r)

let test13 (r : ref U32.t)
  : usteel unit (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    matomic_write_u32 r 0ul;
    matomic_write_u32 r 0ul
  end

////////// errors //////////

#push-options "--silent"
[@@ expect_failure [228]]
let test14 (r0 r1 : ref int)
  : usteel unit (vptr r0) (fun _ -> vptr r0) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    let n = mread r0 in
    mwrite r1 n;
    mwrite r1 0
  end

[@@ expect_failure [228]]
let test15 (r0 r1 : ref int)
  : usteel unit (vptr r0) (fun _ -> vptr r0) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    mwrite r0 0;
    if true
    then mwrite r1 0
    else mwrite r0 0
  end
#pop-options


////////// annotations //////////

let test16 (r : ref int)
  : usteel (ref int) (vptr r) (fun r' -> vptr r') (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    return r
  end

let test17 (r : ref int)
  : usteel (ref int) (vptr r) (fun r' -> vptr r') (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    let r' = return_hint r (fun r' -> [vptr' r' full_perm]) in
    return r'
  end

////////// bind pure generated by req/ens //////////

// During the second run of the tactics, there are several unnecessary bind pure about the ensures of read
let test18 (r : ref int)
  : usteel int (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel #[Dump Stage_M] begin fun () ->
    call read r
  end

// There is no bind pure at all if we use the converted versions
let test18' (r : ref int)
  : usteel int (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel #[Dump Stage_M] begin fun () ->
    mread r
  end

let test19 (b : bool) (r0 r1 : ref int)
  : usteel int (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel #[Dump Stage_M] begin fun () ->
    if b
    then mread r0
    else mread r1
  end
