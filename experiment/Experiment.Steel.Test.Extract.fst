module Experiment.Steel.Test.Extract

module F    = Experiment.Steel.Notations
module M    = Experiment.Steel.Repr.M
module U32  = FStar.UInt32
module Test = Experiment.Steel.Test

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
  = Test.test_ghost r ()
