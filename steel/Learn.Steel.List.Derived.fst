module Learn.Steel.List.Derived

module L = FStar.List.Pure
module G = FStar.Ghost

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.List.DataD
open Learn.Steel.List.Data


let mlist_rew_len #a #opened entry len0 len1 exit
  : SteelGhost unit opened
    (mlist #a entry len0 exit) (fun () -> mlist #a entry len1 exit)
    (requires fun _ -> len0 = len1)
    (ensures  fun h0 () h1 -> sel_list entry len0 exit h0 == sel_list entry len1 exit h1)
  = change_equal_slprop
       (mlist entry len0 exit) (mlist entry len1 exit)


let entry_not_null #a #opened entry len exit
  : SteelGhost unit opened
      (mlist #a entry len exit) (fun () -> mlist #a entry len exit)
      (requires fun _        -> len > 0)
      (ensures  fun h0 () h1 -> frame_equalities (mlist #a entry len exit) h0 h1 /\
                             is_null entry == false)
  =
    mlist_rew_len entry len ((len-1)+1) exit;
    let r1 = elim_mlist_cons entry (len - 1) exit in
    vptr_not_null entry;
    intro_mlist_cons entry r1 (len - 1) exit;
    mlist_rew_len entry ((len-1)+1) len exit


let intro_mlist_sglt #a #opened r0 exit
  : SteelGhost unit opened
      (vptr r0) (fun () -> mlist #a r0 1 exit)
      (requires fun h0       -> (sel r0 h0).next == exit)
      (ensures  fun h0 () h1 -> sel_list r0 1 exit h1 == [r0, (sel r0 h0).data])
  =
    intro_mlist_nil exit;
    intro_mlist_cons r0 exit 0 exit


let rec intro_mlist_append #a #opened r0 (len0 : nat) r1 (len1 : nat) r2
  : SteelGhost unit opened
      (mlist #a r0 len0 r1 `star` mlist #a r1 len1 r2)
      (fun () -> mlist #a r0 (len0+len1) r2)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
        sel_list r0 (len0+len1) r2 h1 == L.(sel_list r0 len0 r1 h0 @ sel_list r1 len1 r2 h0))
      (decreases len0)
  =
    if len0 = 0
    then begin
        mlist_rew_len r0 len0 0 r1;
      elim_mlist_nil r0 r1;
      change_equal_slprop (mlist r1 len1 r2) (mlist r0 (len0+len1) r2)
    end else begin
      let len0' = len0 - 1 in
        mlist_rew_len r0 len0 (len0'+1) r1;
      let r0' = elim_mlist_cons r0 len0' r1 in
      intro_mlist_append r0' len0' r1 len1 r2;
      intro_mlist_cons r0 r0' (len0'+len1) r2;
        mlist_rew_len r0 ((len0'+len1)+1) (len0+len1) r2
    end

let rec elim_mlist_append #a #opened r0 (len len0 len1 : nat) r2 (l0 l1 : list (ref (cell a) & a))
  : SteelGhost (G.erased (ref (cell a))) opened
      (mlist r0 len r2)
      (fun r1 -> mlist r0 len0 r1 `star` mlist r1 len1 r2)
      (requires fun h0 ->
        sel_list r0 len r2 h0 == L.(l0@l1) /\
        L.length l0 = len0 /\ L.length l1 = len1)
      (ensures  fun _ r1 h1 ->
        sel_list r0 len0 r1 h1 == l0 /\
        sel_list r1 len1 r2 h1 == l1)
      (decreases len0)
  =
    if len0 = 0
    then begin
      intro_mlist_nil r0;
        mlist_rew_len r0 0 len0 r0;
      change_equal_slprop (mlist r0 len r2) (mlist r0 len1 r2);
      r0
    end else begin
      let len'  = len  - 1 in
      let len0' = len0 - 1 in
        mlist_rew_len r0 len (len'+1) r2;
      let r0' = elim_mlist_cons r0 len' r2 in
      let r1  = elim_mlist_append r0' len' len0' len1 r2 (L.tl l0) l1 in
      intro_mlist_cons r0 r0' len0' r1;
        mlist_rew_len r0 (len0'+1) len0 r1;
      r1
    end
