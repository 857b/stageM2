module Experiment.Steel.Test.Extract

module U32  = FStar.UInt32
module Test = Experiment.Steel.Monad.Test

open Steel.Effect
open Steel.Reference

let test3 (r0 r1 : ref U32.t)
  : Steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = Test.test3_steel' r0 r1 ()

let test3_LV (r0 r1 : ref U32.t)
  : Steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = Test.test3_LV r0 r1 ()

let test3_LV' (r0 r1 : ref U32.t)
  : Steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r0 `star` vptr r1)
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = Test.test3_LV' r0 r1 ()


let test_ghost (r : ref U32.t)
  : Steel U32.t (vptr r) (fun _ -> vptr r)
      (requires fun _ -> True) (ensures fun h0 _ h1 -> frame_equalities (vptr r) h0 h1)
  = Test.test_ghost0 r ()


let test_slrewrite (r0 r1 r2 : ref U32.t)
  : Steel unit
      (vptr r0 `star` vptr r1) (fun _ -> vptr r2 `star` vptr r1)
      (requires fun _ -> r0 == r2)
      (ensures  fun h0 _ h1 -> sel r0 h0 == sel r2 h1 /\ sel r1 h0 == sel r1 h1)
  = Test.test_slrewrite r0 r1 r2 ()

let test_with_invariant_g (r0 : ghost_ref U32.t) (r1 : ref U32.t) (i : inv (ghost_vptr r0))
  : Steel (Ghost.erased U32.t)
      (vptr r1) (fun _ -> vptr r1)
      (requires fun _ -> True) (ensures fun h0 _ h1 -> frame_equalities (vptr r1) h0 h1)
  = Test.test_with_invariant_g r0 r1 i ()

let test_for_loop_0 (r0 : ref U32.t)
  : Steel unit (vptr r0) (fun _ -> vptr r0) (fun h0 -> True) (fun h0 _ h1 -> True)
  =
    let _ = Test.test_for_loop_0 r0 () in
    ()

// rejected by KRML
//let test_effect (r : ref nat)
//  : Steel unit (vptr r) (fun _ -> vptr r) (requires fun h0 -> sel r h0 > 10) (ensures fun _ _ _ -> True)
//  =
//    Experiment.Steel.Effect.Test.test5' r ()
