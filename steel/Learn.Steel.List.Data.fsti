module Learn.Steel.List.Data

module L = FStar.List.Pure
module M = Steel.Memory
module G = FStar.Ghost

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

open Learn.Steel.List.DataD


(* Separation logic predicate *)

val mlist_sl (#a : Type0) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
  : M.slprop u#1

(* Selector *)

#push-options "--ifuel 1"
val __begin_sg_entry : unit

let sg_entry (#a : Type) (l : list (ref (cell a) & a)) (exit : ref (cell a)) : ref (cell a) =
  match l with
  | [] -> exit
  | hd :: _ -> hd._1

val __end_sg_entry : unit
#pop-options


type mlist_sel_t (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a)) =
  l:list (ref (cell a) & a){L.length l = len /\ sg_entry l exit == entry}

val mlist_sel (#a : Type) (entry : ref (cell a)) (len : nat) (exit : ref (cell a))
  : selector (mlist_sel_t entry len exit) (mlist_sl #a entry len exit)

(* vprop *)

[@@__steel_reduce__]
let mlist' (#a : Type) (entry : ref (cell a)) ([@@@smt_fallback] len : nat) (exit : ref (cell a)) : vprop' =
  {
    hp  = mlist_sl    entry len exit;
    t   = mlist_sel_t entry len exit;
    sel = mlist_sel   entry len exit
  }
unfold let mlist (#a : Type) (entry : ref (cell a)) ([@@@smt_fallback] len : nat) (exit : ref (cell a)) : vprop =
  VUnit (mlist' #a entry len exit)

[@@ __steel_reduce__]
let sel_list (#a:Type0) (#p:vprop) (entry:ref (cell a)) (len : nat) (exit : ref (cell a))
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (mlist entry len exit) /\ True)})
  : GTot (list (ref (cell a) & a))
  = h (mlist entry len exit)

(* intro/elim lemmas *)

val intro_mlist_nil (#a : Type) (#opened:inames) (r0 : ref (cell a))
  : SteelGhost unit opened
      emp (fun () -> mlist r0 0 r0)
      (requires fun _ -> True) (ensures fun _ () h1 -> sel_list r0 0 r0 h1 == [])

val elim_mlist_nil (#a : Type) (#opened:inames) (r0 : ref (cell a)) (r1 : ref (cell a))
  : SteelGhost unit opened
      (mlist r0 0 r1) (fun () -> emp)
      (requires fun _ -> True) (ensures fun _ () _ -> r0 == r1)

val intro_mlist_cons' (#a : Type) (#opened:inames) (r0 r1 : ref (cell a)) (x : a) (len : nat) (exit : ref (cell a))
  : SteelGhost unit opened
     (vptr r0 `star` mlist r1 len exit)
     (fun () -> mlist r0 (len + 1) exit)
     (requires fun h0       -> sel r0 h0 == {next = r1; data = x})
     (ensures  fun h0 () h1 -> sel_list r0 (len + 1) exit h1 == (r0, x) :: sel_list r1 len exit h0)

val intro_mlist_cons (#a : Type) (#opened:inames) (r0 r1 : ref (cell a)) (len : nat) (exit : ref (cell a))
  : SteelGhost unit opened
     (vptr r0 `star` mlist r1 len exit)
     (fun () -> mlist r0 (len + 1) exit)
     (requires fun h0       -> (sel r0 h0).next == r1)
     (ensures  fun h0 () h1 -> sel_list r0 (len + 1) exit h1
                            == (r0, (sel r0 h0).data) :: sel_list r1 len exit h0)

val elim_mlist_cons (#a : Type) (#opened:inames) (r0 : ref (cell a)) (len : nat) (exit : ref (cell a))
  : SteelGhost (G.erased (ref (cell a))) opened
     (mlist r0 (len + 1) exit)
     (fun r1 -> vptr r0 `star` mlist r1 len exit)
     (requires fun _ -> True)
     (ensures  fun h0 r1 h1 ->
      (let l = sel_list r0 (len+1) exit h0 in
       sel r0 h1 == {next = r1; data = (L.hd l)._2} /\
       sel_list r1 len exit h1 == L.tl l))
