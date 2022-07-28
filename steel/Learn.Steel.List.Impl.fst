module Learn.Steel.List.Impl

module L   = FStar.List.Pure
module Ll  = Learn.List
module G   = FStar.Ghost
module U32 = FStar.UInt32

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference
open Learn.Steel.Util

open Learn.Steel.List.Data
open Learn.Steel.List.Derived


(* [length] *)

let rec length (#a : Type) (r : ref (cell a))
  : Steel  U32.t
          (mlistN r) (fun _ -> mlistN r)
          (requires fun h0        -> L.length (sel_listN r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN r) h0 h1 /\
                                  U32.v len = L.length (sel_listN r h0))
  =
    let b = listN_is_nil r in
    if b
    then return 0ul
    else begin
      let r'   = listN_next r in
      let len' = length r'    in
      (**) intro_mlistN_cons r r';
      return U32.(len' +^ 1ul)
    end


(* [insert] *)

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
    if i = 1ul
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


(* alternative version using aptr *)

noextract inline_for_extraction
let insert2_ty (#a : Type) (i : U32.t) (x : ref (cell a)) (r : aptr (ref (cell a))) : Type =
  (entry : G.erased (ref (cell a))) -> (len : G.erased nat) -> (exit : G.erased (ref (cell a))) ->
  Steel (G.erased (ref (cell a)))
        (vptr x `star` r.vp `star` mlist entry len exit)
        (fun entry' -> r.vp `star` mlist entry' (len+1) exit)
        (requires fun h0  -> U32.v i <= len /\
                          aptr_val r h0 == G.reveal entry)
        (ensures  fun h0 entry' h1 ->
                          U32.v i <= len /\
                          aptr_updt r entry' h0 h1 /\
                          sel_list entry' (len+1) exit h1
                            == Ll.insert (U32.v i) (x, (sel x h0).data) (sel_list entry len exit h0))

inline_for_extraction noextract
let insert2_body (#a : Type)
  ($rec_f : (i:U32.t) -> (x : ref (cell a)) -> (r : ref (cell a)) ->
            insert2_ty #a i x (aptr_of_get_set cell_gs_next r))
  (i : U32.t) (x : ref (cell a)) (r : aptr (ref (cell a)))
  : insert2_ty i x r
  = fun g_entry len exit ->
    let entry = r.read () in
    (**) change_equal_slprop (mlist g_entry len exit) (mlist entry len exit);
    if i = 0ul
    then begin
      let x_c = read x in
      write x ({x_c with next = entry});
      (**) intro_mlist_cons x entry len exit;
      r.write x;
      x
    end else begin
      (**) let len' = G.hide (len - 1)                            in
      (**) mlist_rew_len entry len (len'+1) exit;
      (**) let entry'0 = elim_mlist_cons entry len' exit          in
      let entry' = rec_f U32.(i -^ 1ul) x entry entry'0 len' exit in
      (**) intro_mlist_cons entry entry' (len'+1) exit;
      (**) mlist_rew_len entry ((len'+1)+1) (len+1) exit;
      entry
    end

let rec insert2_cell_gs_next (#a : Type) (i : U32.t) (x : ref (cell a)) (r : ref (cell a))
                             (entry : G.erased (ref (cell a))) (len : G.erased nat) (exit : G.erased (ref (cell a)))
                 
  : Steel (G.erased (ref (cell a)))
          (vptr x `star` (aptr_of_get_set cell_gs_next r).vp `star` mlist entry len exit)
          (fun entry' -> (aptr_of_get_set cell_gs_next r).vp `star` mlist entry' (len+1) exit)
          (requires fun h0  -> U32.v i <= len /\
                            aptr_val (aptr_of_get_set cell_gs_next r) h0 == G.reveal entry)
          (ensures  fun h0 entry' h1 ->
                                U32.v i <= len /\
                                aptr_updt (aptr_of_get_set cell_gs_next r) entry' h0 h1 /\
                                sel_list entry' (len+1) exit h1
                                == Ll.insert (U32.v i) (x, (sel x h0).data) (sel_list entry len exit h0))
  = insert2_body #a (insert2_cell_gs_next #a) i x (aptr_of_get_set cell_gs_next r) entry len exit

inline_for_extraction
let insert2 (#a : Type) (i : U32.t) (x : ref (cell a)) (r : aptr (ref (cell a)))
  : insert2_ty #a i x r
  = insert2_body #a (insert2_cell_gs_next #a) i x r

(* [reverse] *)

let rec reverse_aux (#a : Type) (r_f r_r : ref (cell a))
  : Steel (ref (cell a))
          (mlistN r_f `star` mlistN r_r) (fun rt -> mlistN rt)
          (requires fun _ -> True)
          (ensures fun h0 rt h1 ->
             sel_listN rt h1 == L.rev_acc (sel_listN r_f h0) (sel_listN r_r h0))
  =
    let b  = listN_is_nil r_f in
    if b
    then begin
      (**) elim_mlistN_nil r_f;
      return r_r
    end else begin
      let r_f' = listN_next r_f in
      let x_c  = read r_f       in (* TODO? factorize with listN_next *)
      write r_f ({x_c with next = r_r});
      (**) intro_mlistN_cons r_f r_r;
      reverse_aux r_f' r_f
    end

let reverse (#a : Type) (r : ref (cell a))
  : Steel (ref (cell a))
          (mlistN r) (fun rt -> mlistN rt)
          (requires fun _ -> True)
          (ensures fun h0 rt h1 ->
            sel_listN rt h1 == L.rev (sel_listN r h0))
  =
    (**) intro_mlistN_nil null;
    reverse_aux r null

(* ----------------- *)

let length_u32  = length  #U32.t
let insert_u32  = insert  #U32.t
let insert2_u32 (i : U32.t) (x : ref (cell U32.t)) (r : ref (ref (cell U32.t))) =
  insert2 #U32.t i x (aptr_of_vptr r)
let reverse_u32 = reverse #U32.t
