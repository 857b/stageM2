module Experiment.Steel.Test.Extract

module M    = Experiment.Steel.Repr.M
module U32  = FStar.UInt32
module Test = Experiment.Steel.Test

open Steel.Effect
open Steel.Reference


let test3 (r0 r1 : ref U32.t)
  : Steel unit
      (M.vprop_of_list' (Test.test3_mem r0 r1)) (fun _ -> M.vprop_of_list' (Test.test3_mem r0 r1))
      (requires fun h0 -> U32.v (sel r0 h0) < 42)
      (ensures fun h0 () h1 -> U32.v (sel r1 h1) == U32.v (sel r0 h0) + 1)
  = Test.test3_steel' r0 r1 ()
