module Learn.LowStar

module B = LowStar.Buffer
module S = FStar.Seq
module M = LowStar.Modifies
module G   = FStar.Ghost
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

open LowStar.BufferOps
open FStar.HyperStack.ST

let buffer_copy_inv (#a : Type)
     (src dst : B.buffer a) (l : U32.t {B.length src = U32.v l /\ B.length dst = U32.v l})
     h0 h1 (i : nat) =
  B.live h1 src /\ B.live h1 dst
  /\ M.(loc_disjoint (loc_buffer src) (loc_buffer dst))
  /\ M.(modifies (loc_buffer dst) h0 h1)
  /\ S.(forall (j:nat{j < U32.v l}). j < i ==> index (B.as_seq h1 dst) j == index (B.as_seq h1 src) j)

let rec buffer_copy_rec_aux (#a : Type)
     (src dst : B.buffer a) (l : U32.t {B.length src = U32.v l /\ B.length dst = U32.v l})
     h0 (i : U32.t)
  : Stack unit (fun h1 -> buffer_copy_inv src dst l h0 h1 (U32.v i))
               (fun _ () h1 -> buffer_copy_inv src dst l h0 h1 (U32.v l))
               (decreases (U32.v l - U32.v i))
  = if U32.(i <^ l)
    then (dst.(i) <- src.(i);
          buffer_copy_rec_aux src dst l h0 U32.(i +^ 1ul))

let buffer_copy_rec (#a : Type)
  (src dst : B.buffer a) (l : U32.t {B.length src = U32.v l /\ B.length dst = U32.v l})
  : Stack unit
    (requires fun h0 ->
       B.live h0 src /\ B.live h0 dst
    /\ M.(loc_disjoint (loc_buffer src) (loc_buffer dst)))
    (ensures fun h0 () h1 ->
       B.live h1 src /\ B.live h1 dst
    /\ M.(modifies (loc_buffer dst) h0 h1)
    /\ S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
  = let h0 = ST.get () in
    buffer_copy_rec_aux src dst l h0 0ul


(*
let buffer_copy_rec (#a : Type)
  (src dst : B.buffer a) (l : U32.t {B.length src = U32.v l /\ B.length dst = U32.v l})
  : Stack unit
    (requires fun h0 ->
       B.live h0 src /\ B.live h0 dst
    /\ M.(loc_disjoint (loc_buffer src) (loc_buffer dst)))
    (ensures fun h0 () h1 ->
       B.live h1 src /\ B.live h1 dst
    /\ M.(modifies (loc_buffer dst) h0 h1)
    /\ S.equal (B.as_seq h1 dst) (B.as_seq h0 src))
  = 
    let lv : Ghost.erased nat = B.length src in
    let h0 = ST.get() in
    let inv = buffer_copy_inv src dst l h0 in
    let rec copy_i (i : U32.t)
      : Stack unit (fun h1 -> inv h1 (U32.v i)) (fun _ () h1 -> inv h1 lv) (* Ghost.reveal *)
                   (decreases (lv - U32.v i)) =
        if U32.(i <^ l)
        then (assert (U32.v i < B.length src); dst.(i) <- src.(i); copy_i U32.(i +^ 1ul))
    in
    copy_i U32.(0ul)
    (* ALT: C.Loops.for *)
*)

let buffer_copy_uint32 = buffer_copy_rec #U32.t


type test_struct = { fld_a : U32.t; fld_b : U32.t }

let test_set_field (x : B.pointer test_struct)
  : Stack unit (fun h -> B.live h x) (fun _ _ _ -> True) =
  x *= { !*x with fld_a = 1ul }


let test_rt_ghost_callee () : Stack (U32.t & G.erased U32.t) (fun _ -> True) (fun _ _ _ -> True) =
  (0ul, G.hide 1ul)

let test_rt_ghost_caller () : Stack U32.t (fun _ -> True) (fun _ _ _ -> True) =
  (*[@inline_let]*) let (v, gv) = test_rt_ghost_callee () in
  v


inline_for_extraction
let test_struct_arg_callee (p : test_struct) : Stack U32.t (fun _ -> True) (fun _ _ _ -> True)
  = U32.(p.fld_a +%^ p.fld_b)

let test_struct_arg_caller () : Stack U32.t (fun _ -> True) (fun _ _ _ -> True)
  = [@inline_let]let p = {fld_a = 0ul; fld_b = 1ul} in
    test_struct_arg_callee p



(*
let pointer_atomicity (#a : Type) (x y : B.pointer a) :
  Lemma (x == y \/ M.(loc_disjoint (loc_buffer x) (loc_buffer y)))
  = 
    if B.frameOf x = B.frameOf y && B.as_addr x = B.as_addr y then
       ()
*)
