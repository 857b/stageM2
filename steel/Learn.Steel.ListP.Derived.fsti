module Learn.Steel.ListP.Derived

module L  = FStar.List.Pure
module G  = FStar.Ghost
module US = Learn.Steel.Util
module Mem=Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference


open Learn.Steel.ListP.Param
open Learn.Steel.ListP.Data

#set-options "--fuel 2 --ifuel 2"

(*** Pure lemmas *)

let entry_not_null_lem (p : list_param) (entry : ref p.r) len exit m
  : Lemma (requires Mem.interp (hp_of (mlist p entry len exit)) m /\
                    len > 0)
          (ensures  is_null entry == false)
  =
    let hd :: tl = mlist_sel p entry len exit m in
    elim_mlist_cons_lem p entry hd tl (len - 1) exit m;
    p.nnull entry m


(* Not true if the exit is non-null (if there is a loop) *)
let rec mlistN_length_unique (p : list_param) entry len0 len1 m
  : Lemma (requires Mem.interp (hp_of (mlist p entry len0 null)) m /\
                    Mem.interp (hp_of (mlist p entry len1 null)) m)
          (ensures  len0 = len1)
          (decreases len0)
  =
    match mlist_sel p entry len0 null m, mlist_sel p entry len1 null m with
    | [], [] -> ()
    | hd0 :: tl0, hd1 :: tl1 ->
      elim_mlist_cons_lem p entry hd0 tl0 (len0-1) null m;
      elim_mlist_cons_lem p entry hd1 tl1 (len1-1) null m;
      assert (sg_entry tl0 null == sg_entry tl1 null);
      mlistN_length_unique p (sg_entry tl0 null) (len0-1) (len1-1) m
    | [], _ :: _ ->
      assert (entry == null);
      entry_not_null_lem p entry len1 null m
    | _ :: _, [] ->
      assert (entry == null);
      entry_not_null_lem p entry len0 null m


(*** [mlistN] *)

type mlistN_sel_t (p : list_param) (entry : ref p.r) =
  l : list (cell_t p) {entry == sg_entry l null}

val mlistN_sl  (p : list_param u#0) (entry : ref p.r) : Mem.slprop u#1

val mlistN_sel (p : list_param) (entry : ref p.r)
  : selector (mlistN_sel_t p entry) (mlistN_sl p entry)

[@@ __steel_reduce__]
let mlistN' p entry : vprop' = {
  hp  = mlistN_sl    p entry;
  t   = mlistN_sel_t p entry;
  sel = mlistN_sel   p entry
}
unfold let mlistN p entry : vprop = VUnit (mlistN' p entry)

[@@ __steel_reduce__]
let sel_listN (#q:vprop) (p:list_param) (entry:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (mlistN p entry) /\ True)})
  : GTot (mlistN_sel_t p entry)
  = h (mlistN p entry)

val intro_mlistN (#opened:Mem.inames) (p:list_param) (entry:ref p.r) (len : nat)
  : SteelGhost unit opened
      (mlist p entry len null) (fun () -> mlistN p entry)
      (requires fun _ -> True) (ensures fun h0 () h1 -> sel_listN p entry h1 == sel_list p entry len null h0)

val elim_mlistN (#opened:Mem.inames) (p:list_param) (entry:ref p.r)
  : SteelGhost (G.erased nat) opened
      (mlistN p entry) (fun len -> mlist p entry len null)
      (requires fun _ -> True) (ensures fun h0 len h1 -> sel_list p entry len null h1 == sel_listN p entry h0)


(*** Ghost lemmas *)


let mlist_rew_len #opened (p : list_param) entry len0 len1 exit
  : SteelGhost unit opened
      (mlist p entry len0 exit) (fun () -> mlist p entry len1 exit)
      (requires fun _ -> len0 = len1)
      (ensures  fun h0 () h1 -> sel_list p entry len0 exit h0 == sel_list p entry len1 exit h1)
  = change_equal_slprop
       (mlist p entry len0 exit) (mlist p entry len1 exit)

let entry_not_null #opened p entry len exit
  : SteelGhost unit opened
      (mlist p entry len exit) (fun () -> mlist p entry len exit)
      (requires fun _        -> len > 0)
      (ensures  fun h0 () h1 -> frame_equalities (mlist p entry len exit) h0 h1 /\
                             is_null entry == false)
  =
    extract_info_raw (mlist p entry len exit) (is_null entry == false)
                     (entry_not_null_lem p entry len exit)


(** Intro/Elim for [mlist]*)

let intro_mlist_nil #opened (p : list_param) (r0 : ref p.r)
  : SteelGhost unit opened
      emp (fun () -> mlist p r0 0 r0)
      (requires fun _ -> True) (ensures fun _ () h1 -> sel_list p r0 0 r0 h1 == [])
  = change_slprop_rel
      emp (mlist p r0 0 r0) (fun _ l -> l == [])
      (intro_mlist_nil_lem p r0)

let elim_mlist_nil #opened (p : list_param)(r0 r1 : ref p.r)
  : SteelGhost unit opened
      (mlist p r0 0 r1) (fun () -> emp)
      (requires fun _ -> True) (ensures fun h0 () _ -> r0 == r1 /\ sel_list p r0 0 r1 h0 == [])
  = change_slprop_rel
      (mlist p r0 0 r1) emp (fun _ _ -> r0 == r1)
      (fun m -> elim_mlist_nil_lem p r0 r1 m;
             reveal_emp (); Mem.intro_emp m)

let intro_mlist_cons #opened (p : list_param) (r0 r1 : ref p.r) (len : nat) (exit : ref p.r)
  : SteelGhost unit opened
     ((p.cell r0).vp `star` mlist p r1 len exit)
     (fun () -> mlist p r0 (len + 1) exit)
     (requires fun h0       -> g_next p r0 h0 == r1)
     (ensures  fun h0 () h1 -> sel_list p r0 (len + 1) exit h1
                            == (|r0, g_data p r0 h0|) :: sel_list p r1 len exit h0)
  = change_slprop_rel_with_cond
      ((p.cell r0).vp `star` mlist p r1 len exit) (mlist p r0 (len + 1) exit)
      (fun (c, _) -> (p.cell r0).get_next c == r1)
      (fun (c, l0) l1 -> l1 == (|r0, (p.cell r0).get_data c|) :: (l0 <: mlist_sel_t p r1 len exit))
      (intro_mlist_cons_lem p r0 r1 len exit)

let elim_mlist_cons #opened (p : list_param) (r0 : ref p.r) (len : nat) (exit : ref p.r)
  : SteelGhost (G.erased (ref p.r)) opened
     (mlist p r0 (len + 1) exit)
     (fun r1 -> (p.cell r0).vp `star` mlist p r1 len exit)
     (requires fun _ -> True)
     (ensures  fun h0 r1 h1 ->
      (let l  = sel_list p r0 (len+1) exit h0 in
       G.reveal r1 == sg_entry (L.tl l) exit /\
       g_next p r0 h1 == G.reveal r1 /\
       g_data p r0 h1 == (L.hd l)._2 /\
       sel_list p r1 len exit h1 == L.tl l))
  =
    let (l : G.erased (mlist_sel_t p r0 (len+1) exit)) = gget (mlist p r0 (len+1) exit) in
    let hd :: tl = G.reveal l in
    let r1 = sg_entry tl exit in
    change_slprop_rel_with_cond
      (mlist p r0 (len + 1) exit) ((p.cell r0).vp `star` mlist p r1 len exit)
      (fun l0 -> l0 == hd :: tl)
      (fun l0 (c0, l1) ->
        (p.cell r0).get_next c0 == r1 /\
        (p.cell r0).get_data c0 == hd._2 /\
        l1 == tl)
      (elim_mlist_cons_lem p r0 hd tl len exit);
    r1


let intro_mlist_sglt #opened p r0 exit
  : SteelGhost unit opened
      (p.cell r0).vp (fun () -> mlist p r0 1 exit)
      (requires fun h0       -> g_next p r0 h0 == exit)
      (ensures  fun h0 () h1 -> sel_list p r0 1 exit h1 == [(|r0, g_data p r0 h0|)])
  =
    intro_mlist_nil  p exit;
    intro_mlist_cons p r0 exit 0 exit


(** Intro/Elim for [mlistN]*)

let intro_mlistN_nil #opened (p : list_param) (r0 : ref p.r)
  : SteelGhost unit opened
      emp (fun () -> mlistN p r0)
      (requires fun _ -> r0 == null) (ensures fun _ () h1 -> sel_listN p r0 h1 == [])
  = 
    intro_mlist_nil p null;
    intro_mlistN p null 0;
    change_equal_slprop (mlistN p null) (mlistN p r0)

let elim_mlistN_nil #opened (p : list_param) r0
  : SteelGhost unit opened
      (mlistN p r0) (fun () -> emp)
      (* ?requires sel == [], ensures r0 == null *)
      (requires fun _ -> r0 == null) (ensures fun h0 () _ -> sel_listN p r0 h0 == [])
  = let len = elim_mlistN p r0 in
    if len > 0 then entry_not_null p r0 len null else noop ();
      mlist_rew_len p r0 len 0 null;    
    elim_mlist_nil p r0 null

let intro_mlistN_cons #opened (p : list_param) r0 r1
  : SteelGhost unit opened
     ((p.cell r0).vp `star` mlistN p r1)
     (fun () -> mlistN p r0)
     (requires fun h0       -> g_next p r0 h0 == r1)
     (ensures  fun h0 () h1 -> sel_listN p r0 h1
                            == (|r0, g_data p r0 h0|) :: sel_listN p r1 h0)
  = let len = elim_mlistN p r1 in
    intro_mlist_cons p r0 r1 len null;
    intro_mlistN p r0 (len+1)

let elim_mlistN_cons #opened (p : list_param) r0 hd tl
  : SteelGhost (G.erased (ref p.r)) opened
     (mlistN p r0)
     (fun r1 -> (p.cell r0).vp `star` mlistN p r1)
     (requires fun h0 -> sel_listN p r0 h0 == hd :: tl)
     (ensures  fun h0 r1 h1 ->
       r0 == hd._1 /\
       G.reveal r1 == sg_entry tl null /\
       g_next p r0 h1 == G.reveal r1 /\
       g_data p r0 h1 == hd._2 /\
       sel_listN p r1 h1 == tl)
  = let len = elim_mlistN p r0 in
      mlist_rew_len p r0 len ((len-1)+1) null;
    let r1 = elim_mlist_cons p r0 (len-1) null in
    intro_mlistN p r1 (len-1);
    r1


(** append *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1" (* LONG *)
let rec intro_mlist_append #opened p r0 (len0 : nat) r1 (len1 : nat) r2
  : SteelGhost unit opened
      (mlist p r0 len0 r1 `star` mlist p r1 len1 r2)
      (fun () -> mlist p r0 (len0+len1) r2)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 ->
          sel_list p r0 (len0+len1) r2 h1 == L.(sel_list p r0 len0 r1 h0 @ sel_list p r1 len1 r2 h0))
      (decreases len0)
  =
    let h0 = get () in
    if len0 = 0
    then begin
        mlist_rew_len p r0 len0 0 r1;
      elim_mlist_nil p r0 r1;
      change_equal_slprop (mlist p r1 len1 r2) (mlist p r0 (len0+len1) r2);
      let h1 = get () in
      calc (==) {
        sel_list p r0 (len0+len1) r2 h1
          <: list (cell_t p);
      == {}
        sel_list p r1 len1 r2 h0;
      == {}
        L.(sel_list p r0 len0 r1 h0 @ sel_list p r1 len1 r2 h0);
      }
    end else begin
      let len0' = len0 - 1 in
        mlist_rew_len p r0 len0 (len0'+1) r1;
      let r0' = elim_mlist_cons p r0 len0' r1 in
      intro_mlist_append p r0' len0' r1 len1 r2;
      intro_mlist_cons   p r0 r0' (len0'+len1) r2;
        mlist_rew_len p r0 ((len0'+len1)+1) (len0+len1) r2;
      let h1 = get () in
      assert (sel_list p r0 (len0+len1) r2 h1 == L.(sel_list p r0 len0 r1 h0 @ sel_list p r1 len1 r2 h0))
    end

let rec elim_mlist_append #opened (p : list_param) r0 (len len0 len1 : nat) r2 (l0 l1 : list (cell_t p))
  : SteelGhost (G.erased (ref p.r)) opened
      (mlist p r0 len r2)
      (fun r1 -> mlist p r0 len0 r1 `star` mlist p r1 len1 r2)
      (requires fun h0 ->
        sel_list p r0 len r2 h0 == L.(l0@l1) /\
        L.length l0 = len0 /\ L.length l1 = len1)
      (ensures  fun _ r1 h1 ->
        sel_list p r0 len0 r1 h1 == l0 /\
        sel_list p r1 len1 r2 h1 == l1)
      (decreases len0)
  =
    let h0 = get () in
    calc (==) {
      len;
    == {}
      L.length (sel_list p r0 len r2 h0);
    == {}
      L.(length (l0@l1));
    == {}
      len0 + len1;
    };
    if len0 = 0
    then begin
      intro_mlist_nil p r0;
        mlist_rew_len p r0 0 len0 r0;
        mlist_rew_len p r0 len len1 r2;
      r0
    end else begin
      let hd0 :: tl0 = l0 in
      let len'  = len  - 1 in
      let len0' = len0 - 1 in
        mlist_rew_len p r0 len (len'+1) r2;
      let r0' = elim_mlist_cons p r0 len' r2 in
      let r1  = elim_mlist_append p r0' len' len0' len1 r2 tl0 l1 in
      intro_mlist_cons p r0 r0' len0' r1;
        mlist_rew_len p r0 (len0'+1) len0 r1;
      r1
    end
#pop-options


let mlistN_entry_null_iff #opened (p : list_param) entry
  : SteelGhost unit opened
      (mlistN p entry) (fun () -> mlistN p entry)
      (requires fun _ -> True)
      (ensures  fun h0 () h1 -> frame_equalities (mlistN p entry) h0 h1 /\
                             (is_null entry <==> Nil? (sel_listN p entry h0)))
  =
    let l : G.erased (mlistN_sel_t p entry) = gget (mlistN p entry) in
    match G.reveal l with
    | [] -> US.noop_p (mlistN p entry)
    | hd :: tl ->
      let r1 = elim_mlistN_cons p entry hd tl in
      extract_info_raw (p.cell entry).vp (is_null entry == false) (p.nnull entry);
      intro_mlistN_cons p entry r1


(*** non-ghost functions *)

inline_for_extraction
let listN_is_nil (p : list_param) (r0 : ref p.r)
  : Steel  bool
          (mlistN p r0) (fun _ -> mlistN p r0)
          (requires fun _ -> True)
          (ensures  fun h0 b h1 ->
                    frame_equalities (mlistN p r0) h0 h1 /\
                    b = is_null r0 /\
                    (~b ==> Cons? (sel_listN p r0 h0)) /\
                    (b ==> sel_listN p r0 h0 == []))
  = 
    (**) mlistN_entry_null_iff p r0;
    return (is_null #p.r r0)

inline_for_extraction
let list_next (p : list_param) (r0 : ref p.r) (len : G.erased nat) (exit : G.erased (ref p.r))
  : Steel (ref p.r)
          (mlist p r0 (len + 1) exit) (fun r1 -> (p.cell r0).vp `star` mlist p r1 len exit)
          (requires fun _ -> True)
          (ensures  fun h0 r1 h1 ->
                   (let l = sel_list p r0 (len+1) exit h0 in
                    r1 == sg_entry (L.tl l) exit /\
                    g_next p r0 h1 == r1 /\
                    g_data p r0 h1 == (L.hd l)._2 /\
                    sel_list p r1 len exit h1 == L.tl l))
  =
    (**) let g_r1 : G.erased (ref p.r) = elim_mlist_cons p r0 len exit in
    let nxt = (p.cell r0).read_next () in
    (**) change_equal_slprop (mlist p g_r1 len exit)
    (**)                     (mlist p nxt  len exit);
    return nxt

inline_for_extraction
let listN_next (p : list_param) (r0 : ref p.r)
  : Steel (ref p.r)
          (mlistN p r0) (fun r1 -> (p.cell r0).vp `star` mlistN p r1)
          (requires fun h0       -> Cons? (sel_listN p r0 h0))
          (ensures  fun h0 r1 h1 ->
                   (let l = sel_listN p r0 h0 in 
                    Cons? l /\ (* ?need to recall the requires *)
                    r1 == sg_entry (L.tl l) null /\
                    g_next p r0 h1 == r1 /\
                    g_data p r0 h1 == (L.hd l)._2 /\
                    sel_listN p r1 h1 == L.tl l))
  = 
    (**) let l : G.erased (mlistN_sel_t p r0) = gget (mlistN p r0) in
    (**) let g_r1 = elim_mlistN_cons p r0 (L.hd l) (L.tl l) in
    let nxt = (p.cell r0).read_next () in
    (**) change_equal_slprop (mlistN p (G.reveal g_r1))
                             (mlistN p nxt);
    return nxt
