module Learn.LowStar.Queue.Test

module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module U32 = FStar.UInt32
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.Queue

#push-options "--__no_positivity"
noeq
type cell = {
  next: B.pointer_or_null cell;
  data_x: U32.t;
  data_y: bool
}
#pop-options

noextract inline_for_extraction let get_next (x : cell) = x.next
noextract inline_for_extraction let set_next (x : cell) (y : cell_ptr cell) = {x with next = y}

noextract inline_for_extraction
let a : queue_param cell = {
  get_next = get_next;
  set_next = set_next;
  mod_next = (fun x x' -> x.data_x = x'.data_x /\ x.data_y = x'.data_y);
  get_set_next = (fun _ _ -> ());
  set_set_next = (fun _ _ _ -> ());
  mod_refl     = (fun _ -> ());
  mod_set_next = (fun _ _ -> ())
}

type queue = queue cell

let malloc   = malloc   a
let free     = free     a
let is_empty = is_empty a
let enqueue  = enqueue  a get_next set_next
let dequeue  = dequeue  a get_next
inline_for_extraction
let find     = find     a get_next


(* -------------------------------------------------------------- *)


let mem_42 (q : queue) (l : G.erased (cell_list cell))
  : Stack (cell_ptr cell)
          (requires fun h       -> live_queue a h q l)
          (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                    rt == (match Ll.find_gtot (fun (c:B.pointer cell) -> (B.deref h c).data_x = 42ul) l with
                           | Some p -> p | None -> B.null))
  =   let h = ST.get () in
    find q l h (fun c -> (B.deref h c).data_x = 42ul)
               (fun c -> live_queue_content a h q l c; (c.(0ul)).data_x = 42ul)


#push-options "--fuel 3 --z3rlimit 30"
let test_queue_spec () : St unit
  =
    push_frame ();
    let q = malloc HS.root in
    let x0 = B.malloc #cell HS.root ({data_x = 5ul; data_y = true; next = B.null}) 1ul in
    enqueue x0 q [];
      (let h = ST.get () in assert (live_queue a h q [x0]));
      (let d = (x0.(0ul)).data_x in assert (d == 5ul));
      (let f = mem_42 q [x0] in assert (f == B.null));
      (let h0 = ST.get () in
    x0.(0ul) <- {x0.(0ul) with data_x = 42ul};
      (let h1 = ST.get () in
       frame_queue_mod_data a h0 h1 q [x0] (B.loc_buffer x0);
       assert (live_queue a h1 q [x0])));
      (let f = mem_42 q [x0] in assert (f == x0));

    let x12 = B.alloca #cell ({data_x = 7ul; data_y = false; next = B.null}) 2ul in
    let x1 = B.sub x12 0ul 1ul in let x2 = B.sub x12 1ul 1ul in
    enqueue x1 q [x0];
    x2.(0ul) <- {x2.(0ul) with data_y = true};
    let x0' = dequeue q [x0; x1] in
      assert (x0' == x0);
    (*B.free x0; We only have that the queue is disjoint with [loc_buffer x0] but we cannot deduce
                 that it is disjoint with [loc_addr_of_buffer x0] *)
    let x1' = dequeue q [x1] in
      (assert (x1' == x1); let d = (x1.(0ul)).data_x in assert (d = 7ul));
    pop_frame ();
    free q;
    B.free x0
#pop-options
