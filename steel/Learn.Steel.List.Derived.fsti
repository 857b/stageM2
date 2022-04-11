module Learn.Steel.List.Derived

module L  = FStar.List.Pure
module G  = FStar.Ghost
module US = Learn.Steel.Util

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

open Learn.Steel.List.Data


let entry_not_null_lem #a entry len exit m
  : Lemma (requires interp (hp_of (mlist #a entry len exit)) m /\
                    len > 0)
          (ensures  is_null entry == false)
  =
    let hd :: tl = mlist_sel entry len exit m in
    elim_mlist_cons_lem entry hd tl (len - 1) exit m;
    pts_to_not_null entry full_perm ({next = sg_entry tl exit; data = hd._2}) m      

(* Not true if the exit is non-null (if there is a loop) *)
let rec mlistN_length_unique #a entry len0 len1 m
  : Lemma (requires interp (hp_of (mlist #a entry len0 null)) m /\
                    interp (hp_of (mlist #a entry len1 null)) m)
          (ensures  len0 = len1)
          (decreases len0)
  =
    match mlist_sel entry len0 null m, mlist_sel entry len1 null m with
    | [], [] -> ()
    | hd0 :: tl0, hd1 :: tl1 ->
      elim_mlist_cons_lem entry hd0 tl0 (len0-1) null m;
      elim_mlist_cons_lem entry hd1 tl1 (len1-1) null m;
      US.pts_to_ref_injective_and entry full_perm
        ({next = sg_entry tl0 null; data = hd0._2})
        ({next = sg_entry tl1 null; data = hd1._2})
        m;
      assert (sg_entry tl0 null == sg_entry tl1 null);
      mlistN_length_unique (sg_entry tl0 null) (len0-1) (len1-1) m
    | [], _ :: _ ->
      assert (entry == null);
      entry_not_null_lem entry len1 null m
    | _ :: _, [] ->
      assert (entry == null);
      entry_not_null_lem entry len0 null m

(* Ghost lemmas *)

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
  = (* ALT : [extract_info] + [entry_not_null_lem] *)
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
    let h0 = get () in
    if len0 = 0
    then begin
        mlist_rew_len r0 len0 0 r1;
      elim_mlist_nil r0 r1;
      change_equal_slprop (mlist r1 len1 r2) (mlist r0 (len0+len1) r2);
      let h1 = get () in
      assert (sel_list r0 (len0+len1) r2 h1 == L.(sel_list r0 len0 r1 h0 @ sel_list r1 len1 r2 h0))
    end else begin
      let len0' = len0 - 1 in
        mlist_rew_len r0 len0 (len0'+1) r1;
      let r0' = elim_mlist_cons r0 len0' r1 in
      intro_mlist_append r0' len0' r1 len1 r2;
      intro_mlist_cons r0 r0' (len0'+len1) r2;
        mlist_rew_len r0 ((len0'+len1)+1) (len0+len1) r2;
      let h1 = get () in
      assert (sel_list r0 (len0+len1) r2 h1 == L.(sel_list r0 len0 r1 h0 @ sel_list r1 len1 r2 h0))
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
    let h0 = get () in
    calc (==) {
      len;
    == {}
      L.length (sel_list r0 len r2 h0);
    == {}
      L.(length (l0@l1));
    == {}
      len0 + len1;
    };
    if len0 = 0
    then begin
      intro_mlist_nil r0;
        mlist_rew_len r0 0 len0 r0;
      change_equal_slprop (mlist r0 len r2) (mlist r0 len1 r2);
      r0
    end else begin
      let hd0 :: tl0 = l0 in
      let len'  = len  - 1 in
      let len0' = len0 - 1 in
        mlist_rew_len r0 len (len'+1) r2;
      let r0' = elim_mlist_cons r0 len' r2 in
      let r1  = elim_mlist_append r0' len' len0' len1 r2 tl0 l1 in
      intro_mlist_cons r0 r0' len0' r1;
        mlist_rew_len r0 (len0'+1) len0 r1;
      r1
    end


(* [mlistN] *)

type mlistN_sel_t (#a : Type) (entry : ref (cell a)) =
  l : list (ref (cell a) & a) {entry == sg_entry l null}

val mlistN_sl (#a : Type0) (entry : ref (cell a)) : slprop u#1

val mlistN_sel (#a : Type) (entry : ref (cell a))
  : selector (mlistN_sel_t entry) (mlistN_sl #a entry)

[@@ __steel_reduce__]
let mlistN' #a entry : vprop' = {
  hp  = mlistN_sl    #a entry;
  t   = mlistN_sel_t #a entry;
  sel = mlistN_sel   #a entry
}
unfold let mlistN #a entry : vprop = VUnit (mlistN' #a entry)

[@@ __steel_reduce__]
let sel_listN (#a:Type0) (#p:vprop) (entry:ref (cell a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (mlistN entry) /\ True)})
  : GTot (mlistN_sel_t #a entry)
  = h (mlistN entry)

val intro_mlistN (#a:Type) (#opened:inames) (entry:ref (cell a)) (len : nat)
  : SteelGhost unit opened
      (mlist #a entry len null) (fun () -> mlistN entry)
      (requires fun _ -> True) (ensures fun h0 () h1 -> sel_listN entry h1 == sel_list entry len null h0)

val elim_mlistN (#a:Type) (#opened:inames) (entry:ref (cell a))
  : SteelGhost (G.erased nat) opened
      (mlistN #a entry) (fun len -> mlist entry len null)
      (requires fun _ -> True) (ensures fun h0 len h1 -> sel_list entry len null h1 == sel_listN entry h0)

let intro_mlistN_nil #a #opened (r0 : ref (cell a))
  : SteelGhost unit opened
      emp (fun () -> mlistN #a r0)
      (requires fun _ -> r0 == null) (ensures fun _ () h1 -> sel_listN #a r0 h1 == [])
  = 
    intro_mlist_nil #a null;
    intro_mlistN #a null 0;
    change_equal_slprop (mlistN #a null) (mlistN #a r0)

let elim_mlistN_nil #a #opened r0
  : SteelGhost unit opened
      (mlistN #a r0) (fun () -> emp)
      (requires fun _ -> r0 == null) (ensures fun h0 () _ -> sel_listN r0 h0 == [])
  = let len = elim_mlistN r0 in
    if len > 0 then entry_not_null r0 len null else noop (); (* need a else branch *)
      mlist_rew_len r0 len 0 null;    
    elim_mlist_nil r0 null

let intro_mlistN_cons #a #opened r0 r1
  : SteelGhost unit opened
     (vptr r0 `star` mlistN #a r1)
     (fun () -> mlistN r0)
     (requires fun h0       -> (sel r0 h0).next == r1)
     (ensures  fun h0 () h1 -> sel_listN r0 h1
                            == (r0, (sel r0 h0).data) :: sel_listN r1 h0)
  = let len = elim_mlistN r1 in
    intro_mlist_cons r0 r1 len null;
    intro_mlistN r0 (len+1)

let elim_mlistN_cons #a #opened r0 hd tl
  : SteelGhost (G.erased (ref (cell a))) opened
     (mlistN r0)
     (fun r1 -> vptr r0 `star` mlistN r1)
     (requires fun h0 -> sel_listN r0 h0 == hd :: tl)
     (ensures  fun h0 r1 h1 ->
       G.reveal r1 == sg_entry tl null /\
       sel r0 h1 == {next = r1; data = hd._2} /\
       sel_listN r1 h1 == tl)
  = let len = elim_mlistN r0 in
      mlist_rew_len r0 len ((len-1)+1) null;
    let r1 = elim_mlist_cons r0 (len-1) null in
    intro_mlistN r1 (len-1);
    r1


let mlistN_entry_null_iff #a #opened entry
  : SteelGhost unit opened
      (mlistN #a entry) (fun () -> mlistN #a entry)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 -> frame_equalities (mlistN #a entry) h0 h1 /\
                             (is_null entry <==> Nil? (sel_listN entry h0)))
  =
    let l : G.erased (mlistN_sel_t entry) = gget (mlistN entry) in
    match G.reveal l with
    | [] -> US.noop_p (mlistN entry)
    | hd :: tl ->
      let r1 = elim_mlistN_cons entry hd tl in
      vptr_not_null entry;
      intro_mlistN_cons entry r1


(* non-ghost functions *)

inline_for_extraction
let listN_is_nil #a (r0 : ref (cell a))
  : Steel  bool
          (mlistN #a r0) (fun _ -> mlistN #a r0)
          (requires fun _ -> True)
          (ensures  fun h0 b h1 ->
                    frame_equalities (mlistN #a r0) h0 h1 /\
                    b = is_null r0 /\
                    (~b ==> Cons? (sel_listN r0 h0)) /\
                    (b ==> sel_listN r0 h0 == []))
  = 
    (**) mlistN_entry_null_iff r0;
    return (is_null #(cell a) r0)

inline_for_extraction
let list_next #a (r0 : ref (cell a)) (len : G.erased nat) (exit : G.erased (ref (cell a)))
  : Steel (ref (cell a))
          (mlist r0 (len + 1) exit) (fun r1 -> vptr r0 `star` mlist r1 len exit)
          (requires fun _ -> True)
          (ensures  fun h0 r1 h1 ->
                   (let l = sel_list r0 (len+1) exit h0 in
                    r1 == sg_entry (L.tl l) exit /\
                    sel r0 h1 == {next = r1; data = (L.hd l)._2} /\
                    sel_list r1 len exit h1 == L.tl l))
  =
    (**) let g_r1 : G.erased (ref (cell a)) = elim_mlist_cons r0 len exit in
    let c0 = read r0 in
    (**) change_equal_slprop (mlist (G.reveal g_r1) (G.reveal len) (G.reveal exit))
    (**)                     (mlist c0.next (G.reveal len) (G.reveal exit));
    return c0.next

inline_for_extraction
let listN_next #a (r0 : ref (cell a))
  : Steel (ref (cell a))
          (mlistN r0) (fun r1 -> vptr r0 `star` mlistN r1)
          (requires fun h0       -> Cons? (sel_listN r0 h0))
          (ensures  fun h0 r1 h1 ->
                   (let l = sel_listN r0 h0 in 
                    Cons? l /\ (* ?need to recall the requires *)
                    r1 == sg_entry (L.tl l) null /\
                    sel r0 h1 == {next = r1; data = (L.hd l)._2} /\
                    sel_listN r1 h1 == L.tl l))
  = 
    (**) let l : G.erased (mlistN_sel_t r0) = gget (mlistN r0) in
    (**) let g_r1 = elim_mlistN_cons r0 (L.hd l) (L.tl l) in
    let c0 = read r0 in
    (**) change_equal_slprop (mlistN (G.reveal g_r1)) (mlistN c0.next);
    return c0.next
