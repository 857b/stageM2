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

noextract
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

inline_for_extraction
type test_struct = { fld_a : U32.t; fld_b : U32.t }

let test_set_field (x : B.pointer test_struct)
  : Stack unit (fun h -> B.live h x) (fun _ _ _ -> True) =
  let xv = x.(0ul) in
  x.(0ul) <- { xv with fld_a = 1ul }


let test_rt_ghost_callee () : Stack (U32.t & G.erased U32.t) (fun _ -> True) (fun _ _ _ -> True) =
  (0ul, G.hide 1ul)

let test_rt_ghost_caller () : Stack U32.t (fun _ -> True) (fun _ _ _ -> True) =
  (*[@inline_let]*) let (v, gv) = test_rt_ghost_callee () in
  v

let test_ghost_pair () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let x = B.alloca #(U32.t & G.erased nat) (0ul, G.hide 0) 1ul in
  x.(0ul) <- (U32.((x.(0ul))._1 +^ 1ul), G.hide 1);
  pop_frame ()


inline_for_extraction
let test_struct_arg_callee (p : test_struct) : Stack U32.t (fun _ -> True) (fun _ _ _ -> True)
  = U32.(p.fld_a +%^ p.fld_b)

let test_struct_arg_caller () : Stack U32.t (fun _ -> True) (fun _ _ _ -> True)
  = [@inline_let]let p = {fld_a = 0ul; fld_b = 1ul} in
    test_struct_arg_callee p

let test_struct_arg () : Stack U32.t (fun _ -> True) (fun _ _ _ -> True)
  = ({fld_a = 0ul; fld_b = 1ul}).fld_a


(*
let pointer_atomicity (#a : Type) (x y : B.pointer a) :
  Lemma (x == y \/ M.(loc_disjoint (loc_buffer x) (loc_buffer y)))
  = 
    if B.frameOf x = B.frameOf y && B.as_addr x = B.as_addr y then
       ()

pointer_distinct_sel_disjoint
Heap.lemma_sel_same_address
*)


let test_stateful_loop_guard (b : bool) : Stack unit (requires fun _ -> True) (ensures fun _ _ _ -> True)
  =
    push_frame ();
    let x = B.alloca #U32.t 0ul 1ul in
    let test () : Stack bool (requires fun h -> B.live h x) (ensures fun _ b h -> B.live h x)
      = x.(0ul) <- 1ul; b
    in
    C.Loops.while #(fun h -> B.live h x) #(fun _ h -> B.live h x)
      test (fun () -> ());
    pop_frame ()


(* to be extracted with -ftail-calls *)
(* noextract inline_for_extraction *)
let rec tail_recursive (acc : U32.t) (i : U32.t) : Stack U32.t (requires fun _ -> True) (ensures fun _ _ _ -> True)
  =
    if U32.(i >^ 0ul)
    then tail_recursive U32.(acc +%^ i) U32.(i -^ 1ul)
    else acc

let inline_tail_call (i : U32.t) : Stack U32.t (requires fun _ -> True) (ensures fun _ _ _ -> True)
  =
    U32.(tail_recursive 0ul i +%^ 1ul)


(* ---------- *)

inline_for_extraction
let ret_buf () : Stack bool (fun _ -> True) (fun _ _ _ -> True) =
  push_frame ();
  let b = B.alloca #bool true 1ul in
  (* ... *)
  let rt = b.(0ul) in
  pop_frame ();
  rt

let ret_buf_caller () : Stack bool (fun _ -> True) (fun _ _ _ -> True) =
  ret_buf ()

(* ----------- *)

let rec f_call_u32 (a : Type) (x : a) (b:bool) : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  if b then f_call_u32 U32.t 0ul false

let f_call_u32_caller () : Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  f_call_u32 bool false true
