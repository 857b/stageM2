module Learn.LowStar.Queue

module UL   = Learn.LowStar.Util
module M    = LowStar.Modifies
module Prop = Learn.LowStar.Queue.Prop
module Impl = Learn.LowStar.Queue.Impl

type queue c = Prop.queue c

let loc_queue_st #c q =
  M.loc_addr_of_buffer q
let loc_queue #c q l =
  M.(loc_union (loc_addr_of_buffer q) (Prop.loc_seg l))
let wf_queue #c q l =
  Prop.wf_seg l /\ M.(loc_disjoint (loc_addr_of_buffer q) (Prop.loc_seg l))
let live_queue    = Prop.live_queue
let freeable #c q = B.freeable q /\ True

noextract inline_for_extraction let malloc #c a r =
  (**) assert (Prop.loc_seg #c [] == M.loc_none);
  Impl.malloc #c a r

noextract inline_for_extraction let free     = Impl.free
noextract inline_for_extraction let is_empty = Impl.is_empty

noextract inline_for_extraction let enqueue #c a x q l =
  Impl.enqueue #c a x q l;
  (**) let l' = L.snoc (G.reveal l,x) in
  (**) Prop.append_seg_wf l [x];
  (**) Prop.append_seg_loc l [x];
  (**) M.loc_union_assoc (M.loc_addr_of_buffer q) (Prop.loc_seg l) (Prop.loc_seg [x])

noextract inline_for_extraction let dequeue #c a q l =
  let rt = Impl.dequeue #c a q l in
  (**) UL.loc_union_comm12 (M.loc_addr_of_buffer q) (M.loc_buffer rt) (Prop.loc_seg (L.tl l));
  rt

noextract inline_for_extraction let find     = Impl.find


let loc_queue_live_in #c a h q l =
  Prop.loc_seg_live_in a h (Prop.sg_of_cells l)

let frame_queue #c a h0 h1 q l r =
  Prop.frame_seg #c a h0 h1 (Prop.sg_of_cells l) r

let frame_queue_mod_data #c a h0 h1 q l r =
  Prop.frame_seg_mod_data #c a h0 h1 (Prop.sg_of_cells l)

let loc_queue_content #c q l x =
  Prop.loc_seg_cell l x

let live_queue_content #c a h q l x =
  Prop.live_seg_cell a h (Prop.sg_of_cells l) x
