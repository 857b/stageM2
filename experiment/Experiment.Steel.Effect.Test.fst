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
let dump_repr (#a : Type) (#r : prog_tree a) (ek : SH.effect_kind)
      ($re : unit -> MRepr a ek r None LocationP)
      (#[(norm [delta_attr [`%__repr_M__]; iota]; dump "dump_repr"; exact (`()))] d : display_term r)
      ()
  : unit
  = ()


// We need to annotate [SH.KGhostI Set.empty] otherwise the infered effect is [SH.KGhostI ?opened] and
// ?opened is not constrained
// This raise a non-fatal GOAL IS ALREADY SOLVED error
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


// Stack overflow
//let test2 (r : ref int) =
//  dump_repr SH.KSteel (fun () -> let x = call read r in return x) ()

//let test3 (b : bool) (r0 r1 : ref int) =
//  dump_repr (fun () -> if b then let x = read r0 in return x
//                         else let x = read r1 in return x)

let test3' (b : bool) (r0 r1 : ref int)
  : usteel int (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
         (requires fun h0 -> sel r0 h0 >= 0 /\ sel r1 h0 >= 0)
         (ensures  fun h0 x h1 -> frame_equalities (vptr r0 `star` vptr r1) h0 h1 /\ x >= 0)
  = to_steel begin fun () ->
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


let test6 (opened : Mem.inames) (r : ghost_ref int) (x : int)
  : usteel_ghost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    call_g (ghost_write r) x;
    call_g (ghost_write r) x
  end

// Since MReprGhost is erasable, we can use ghost operations
let test7 (opened: Mem.inames) (r : ghost_ref int)
  : usteel_ghost int opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    let x = call_g ghost_read r in
    Ghost.reveal x
  end

let test8 (opened : Mem.inames) (r : ghost_ref int) (b : bool) (x0 x1 : int)
  : usteel_ghost unit opened
      (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    if b
    then call_g (ghost_write r) x0
    else call_g (ghost_write r) x1
  end

let test9 (r : ghost_ref int) (x : int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    call_g (ghost_write r) x
  end

let test9' (r : ghost_ref int) (x : int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    call_g (ghost_write r) x;
    return ()
  end

let test10 (r0 r1 : ref U32.t)
  : usteel unit (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun _ -> True)
      (ensures fun h0 () h1 -> sel r0 h1 = sel r1 h0 /\ sel r1 h1 = sel r0 h0)
  = to_steel begin fun () ->
    // note: using match blocks some reductions
    //let () = () in
    let x0 = call read r0 in
    let x1 = call read r1 in
    call (write r0) x1;
    call (write r1) x0
  end

[@@ expect_failure]
let test11 #opened (r : ref int)
  : usteel_ghost unit opened (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel_g begin fun () ->
    call (write r) 0
  end

[@@ expect_failure]
let test12 (r : ghost_ref int)
  : usteel unit (ghost_vptr r) (fun _ -> ghost_vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    let x = call_g ghost_read r in
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

let test13 (r : ref U32.t)
  : usteel unit (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    call_a (atomic_write_u32 r) 0ul;
    call_a (atomic_write_u32 r) 0ul
  end

////////// errors //////////

#push-options "--silent"
[@@ expect_failure [228]]
let test14 (r0 r1 : ref int)
  : usteel unit (vptr r0) (fun _ -> vptr r0) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    call (write r0) 0;
    call (write r1) 0
  end

[@@ expect_failure [228]]
let test15 (r0 r1 : ref int)
  : usteel unit (vptr r0) (fun _ -> vptr r0) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel begin fun () ->
    call (write r0) 0;
    if true
    then call (write r1) 0
    else call (write r0) 0
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

unfold
let call_read (#a : Type) (#[@@@ __mrepr_implicit__] loc : location_goal []) (r : ref a)
  : MRepr a SH.KSteel
      (M.Tspec a (M.spec_r_steel u#0 u#8 (vptr r) (fun _ -> vptr r) (fun _ -> True)
                 (fun h0 x h1 -> sel r h0 == sel r h1 /\ x == sel r h1)))
      None (locm loc)
  = MRepr?.reflect
      (mk_repr (Experiment.Steel.Combinators.repr_of_steel _ _ _ _ (SH.steel_fe (fun () -> read r))))

// There is no bind pure at all here
let test18' (r : ref int)
  : usteel int (vptr r) (fun _ -> vptr r) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel #[Dump Stage_M] begin fun () ->
    call_read r
  end

let test19 (b : bool) (r0 r1 : ref int)
  : usteel int (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1) (fun _ -> True) (fun _ _ _ -> True)
  = to_steel #[Dump Stage_M] begin fun () ->
    if b
    then call_read r0
    else call_read r1
  end
