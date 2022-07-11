module Learn.Steel.DLList.Test

module U32 = FStar.UInt32

open FStar.Ghost
open Steel.Effect
open Steel.Reference
open Learn.Steel.DLList

noeq
type cell0 = {
  prv : ref cell0;
  nxt : ref cell0;
  data0 : bool;
  data1 : U32.t;
}

inline_for_extraction noextract
let p0 : list_param
  = list_param_of_vptr cell0 (bool & U32.t)
      (fun s -> {cl_prv = s.prv; cl_nxt = s.nxt; cl_data = (s.data0, s.data1)})
      (fun s prv -> {s with prv})
      (fun s nxt -> {s with nxt})

let p0_remove = remove p0
