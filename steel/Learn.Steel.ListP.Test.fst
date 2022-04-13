module Learn.Steel.ListP.Test

module L   = FStar.List.Pure
module U32 = FStar.UInt32

open Steel.Effect
open Steel.Reference

open Learn.Steel.ListP

#push-options "--__no_positivity"
noeq
type cell0 = {
  next: ref cell0;
  data_x: U32.t;
  data_y: bool
}
#pop-options

inline_for_extraction noextract
let p0 : list_param =
  list_param_of_vptr cell0 (U32.t & bool)
    ({get = (fun c -> c.next); set = (fun c x -> {c with next = x})})
    (fun c   -> (c.data_x, c.data_y))

let rec p0_length (r : ref cell0)
  : Steel  U32.t
          (mlistN p0 r) (fun _ -> mlistN p0 r)
          (requires fun h0        -> L.length (sel_listN p0 r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN p0 r) h0 h1 /\
                                  U32.v len = L.length (sel_listN p0 r h0))
  = length_body p0 p0_length r

noextract
let p0_reverse (r : ref cell0)
  : Steel (ref cell0)
          (mlistN p0 r) (fun rt -> mlistN p0 rt)
          (requires fun _ -> True)
          (ensures fun h0 rt h1 -> sel_listN p0 rt h1 == L.rev (sel_listN p0 r h0))
  = reverse p0 r
