module Learn.Steel.List.Impl

module L   = FStar.List.Pure
module Ll  = Learn.List
module G   = FStar.Ghost
module U32 = FStar.UInt32

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.List.DataD
open Learn.Steel.List.Data
open Learn.Steel.List.Derived


let rec length (#a : Type) (r : ref (cell a))
  : Steel  U32.t
          (mlistN r) (fun _ -> mlistN r)
          (requires fun h0        -> L.length (sel_listN r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN r) h0 h1 /\
                                  U32.v len = L.length (sel_listN r h0))
  =
    let b  = listN_is_nil r in
    if b
    then return 0ul
    else begin
      let r'   = listN_next r in
      let len' = length r'    in
      (**) intro_mlistN_cons r r';
      return U32.(len' +^ 1ul)
    end


let rec insert_aux (#a : Type) (i : U32.t) (x : ref (cell a))
                   (entry : ref (cell a)) (len : G.erased nat) (exit : G.erased (ref (cell a)))
  : Steel  unit
          (vptr x `star` mlist entry len exit) (fun () -> mlist entry (len+1) exit)
          (requires fun _        -> 1 <= U32.v i /\ U32.v i <= len)
          (ensures  fun h0 () h1 -> U32.v i <= len /\
                                 sel_list entry (len+1) exit h1
                                   == Ll.insert (U32.v i) (x, (sel x h0).data) (sel_list entry len exit h0))
  =
    (**) let len1 = G.hide (len - 1) in
    (**) mlist_rew_len entry len (len1+1) exit;
    let nxt = list_next entry len1 exit in
    if U32.v i = 1
    then begin
      let x_c = read x in
      write x ({x_c with next = nxt});
      (**) intro_mlist_cons x nxt len1 exit;
      let entry_c = read entry in
      write entry ({entry_c with next = x});
      (**) intro_mlist_cons entry x (len1+1) exit
    end else begin
      insert_aux U32.(i -^ 1ul) x nxt len1 exit;
      (**) intro_mlist_cons entry nxt (len1+1) exit
    end;
    (**) mlist_rew_len entry ((len1+1)+1) (len+1) exit

let insert (#a : Type) (i : U32.t) (x : ref (cell a))
           (entry : ref (cell a)) (len : G.erased nat) (exit : G.erased (ref (cell a)))
  : Steel (ref (cell a))
          (vptr x `star` mlist entry len exit) (fun rt -> mlist rt (len+1) exit)
          (requires fun _        -> U32.v i <= len)
          (ensures  fun h0 rt h1 -> U32.v i <= len /\
                                 sel_list rt (len+1) exit h1
                                   == Ll.insert (U32.v i) (x, (sel x h0).data) (sel_list entry len exit h0))
  =
    if i = 0ul then begin
      let x_c = read x in
      write x ({x_c with next = entry});
      (**) intro_mlist_cons x entry len exit;
      return x
    end else begin
      insert_aux i x entry len exit;
      entry
    end


(* ----------------- *)

let length_u32 = length #U32.t
let insert_u32 = insert #U32.t
