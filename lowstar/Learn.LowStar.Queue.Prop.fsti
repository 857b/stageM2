module Learn.LowStar.Queue.Prop

module L   = FStar.List.Pure
module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.Queue.Param


noeq
type queue_st (c : Type) = {
  q_exit  : cell_ptr c;
  q_entry : cell_ptr c;
}

type queue (c : Type) = B.pointer (queue_st c)

let g_cell_next (#c : Type) (a : queue_param c) (h : HS.mem) (p : B.pointer c) : GTot (cell_ptr c)
  = a.get_next (B.deref h p)


(** Ghost representation of the structures *)

noextract noeq
type list_seg (c : Type) = {
  segment : list (B.pointer c);
  exit    : cell_ptr c
}

let list_nil (c : Type) : Type = sg:list_seg c{sg.exit == B.null}

let sg_of_cells (#c : Type) (l : cell_list c) : list_nil c
  = { segment = l; exit = B.null }


let sg_entry (#c : Type) (sg : list_seg c) : Tot (cell_ptr c)
  = match sg.segment with
    | []    -> sg.exit
    | hd :: _ -> hd

let cons_seg (#c : Type) (hd : B.pointer c) (sg : list_seg c) : list_seg c
  = { sg with segment = hd :: sg.segment }

let tail_seg (#c : Type) (sg : list_seg c)
  : Pure (list_seg c) (requires Cons? sg.segment) (ensures fun _ -> True)
  = {sg with segment = L.tail sg.segment}

let append_seg (#c : Type) (sg0 sg1 : list_seg c) : Tot (list_seg c)
  = { segment = L.(sg0.segment @ sg1.segment);
      exit    = sg1.exit }

let append_seg_assoc (#c : Type) (sg0 sg1 sg2 : list_seg c)
  : Lemma (ensures append_seg sg0 (append_seg sg1 sg2) == append_seg (append_seg sg0 sg1) sg2)
  = L.append_assoc sg0.segment sg1.segment sg2.segment

let rec last_cell (#c : Type) (sg : cell_list c)
  : Pure (cell_ptr c)
         (requires True)
         (ensures fun lt -> B.g_is_null lt <==> Nil? sg)
         (decreases sg)
  = match sg with
    | []     -> B.null
    | [c]    -> c
    | _ :: tl -> last_cell tl


(** Predicates *)

let rec loc_seg (#c : Type) (sg : cell_list c) : GTot M.loc
  (decreases sg)
  = match sg with
    | [] -> M.loc_none
    | hd :: tl -> M.(loc_union (loc_buffer hd) (loc_seg tl))

let rec wf_seg (#c : Type) (sg : cell_list c) : Tot prop
  (decreases sg)
  = match sg with
    | [] -> True
    | hd :: tl -> (M.loc_disjoint (B.loc_buffer hd) (loc_seg tl))
             /\ wf_seg tl

let rec live_seg_def (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: _ -> let sg' = tail_seg sg in
               B.live h hd /\ g_cell_next a h hd == sg_entry sg' /\ live_seg_def a h sg'

(* ALT? [@@"opaque_to_smt"] + reveal_opaque *)
val live_seg (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c) : Tot prop

val live_seg_unfold : #c:Type -> (a : queue_param c) -> Lemma (live_seg a == live_seg_def a)


/// A queue is a [queue_st] with a linked list of [cell].
///   The first element of the list is the older element.
///   - [q_exit] points to the entry of the list.
///   - [q_entry] points to the last element of the list (or null if the queue is empty)
///     ALT? unspecified if the queue is empty

let loc_queue (#c : Type) (q : queue c) (l : cell_list c) : GTot M.loc =
  M.(loc_union (loc_buffer q) (loc_seg l))

let wf_queue (#c : Type) (q : queue c) (l : cell_list c) : Tot prop =
  wf_seg l /\ M.(loc_disjoint (loc_buffer q) (loc_seg l))

let live_queue (#c : Type) (a : queue_param c) (h : HS.mem) (q : queue c) (l : cell_list c) : Tot prop =
  B.live h q /\ live_seg a h (sg_of_cells l) /\
 (let qs = B.deref h q in
  qs.q_exit  == sg_entry (sg_of_cells l) /\
  qs.q_entry == last_cell l)


(** Lemmas about the predicates *)

val loc_seg_live_in (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c)
  : Lemma (requires live_seg a h sg) (ensures B.loc_in (loc_seg sg.segment) h)
          (decreases sg.segment)
    [SMTPat (live_seg a h sg)]

val loc_seg_cell (#c : Type) (sg : cell_list c) (x : B.pointer c)
  : Lemma (requires  L.memP x sg)
          (ensures   M.(loc_seg sg `loc_includes` loc_buffer x))
          (decreases sg)

val live_seg_cell (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c) (x : B.pointer c)
  : Lemma (requires  live_seg a h sg /\ L.memP x sg.segment)
          (ensures   B.live h x)
          (decreases sg.segment)

val frame_seg (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (sg : list_seg c) (r : B.loc)
  : Lemma (requires live_seg a h0 sg /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_seg sg.segment)))
          (ensures  live_seg a h1 sg)
          (decreases sg.segment)
    [SMTPat (live_seg a h0 sg); SMTPat (M.modifies r h0 h1)]

val frame_seg_mod_data (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (sg : list_seg c)
  : Lemma (requires live_seg a h0 sg /\ mod_data_list a h0 h1 sg.segment)
          (ensures  live_seg a h1 sg)
          (decreases sg.segment)

val disjoint_mod_next_seg (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (p : M.loc) (sg : list_seg c)
  : Lemma (requires  M.(loc_disjoint (loc_seg sg.segment) p /\
                        live_seg a h0 sg /\ modifies p h0 h1))
          (ensures   mod_next_list a h0 h1 sg.segment)
          (decreases sg.segment)



let rec append_seg_loc (#c : Type) (sg0 sg1 : cell_list c)
  : Lemma (ensures loc_seg L.(sg0@sg1) == M.loc_union (loc_seg sg0) (loc_seg sg1))
          (decreases sg0)
          [SMTPat (loc_seg L.(sg0@sg1))]
  = match sg0 with
    | [] -> ()
    | hd :: tl ->
      append_seg_loc tl sg1;
      M.loc_union_assoc (M.loc_buffer hd) (loc_seg tl) (loc_seg sg1)

let rec append_seg_wf (#c : Type) (sg0 sg1 : cell_list c)
  : Lemma (ensures wf_seg L.(sg0@sg1) <==>
                   wf_seg sg0 /\ wf_seg sg1 /\ M.loc_disjoint (loc_seg sg0) (loc_seg sg1))
          (decreases sg0)
          [SMTPat (wf_seg L.(sg0@sg1))]
  = match sg0 with
    | [] -> ()
    | _ :: tl -> append_seg_wf tl sg1

val append_seg_live (#c : Type) (a : queue_param c) (h : HS.mem) (sg0 sg1 : list_seg c)
  : Lemma (requires sg0.exit == sg_entry sg1)
          (ensures live_seg a h (append_seg sg0 sg1) <==> live_seg a h sg0 /\ live_seg a h sg1)
          (decreases sg0.segment)

val last_cell_live (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c)
  : Lemma (requires live_seg a h sg)
          (ensures B.live h (last_cell sg.segment))
          (decreases sg.segment)

(** Segments handling *)

noextract let empty_seg  (#c : Type) (exit : cell_ptr c) = { segment = []; exit }
noextract let empty_list (c : Type) : list_nil c = empty_seg B.null
val empty_live (#c : Type) (a : queue_param c) (exit : cell_ptr c) (h : HS.mem)
  : Lemma (live_seg a h (empty_seg #c exit)) [SMTPat (live_seg a h (empty_seg #c exit))]

let empty_sg_of_cell (#c : Type)
  : Lemma (sg_of_cells #c [] == empty_list c) [SMTPat (sg_of_cells #c [])]
  = ()

val sg_mkcons_lem (#c : Type) (a : queue_param c) (h : HS.mem) (hd : B.pointer c) (tl : list_seg c)
  : Lemma (requires B.live h hd /\
                    g_cell_next a h hd == sg_entry tl /\
                    live_seg a h tl)
          (ensures  live_seg a h (cons_seg hd tl))

val sg_uncons_lem (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c)
  : Lemma (requires live_seg a h sg /\ Cons? sg.segment)
          (ensures  (let cell = L.hd sg.segment in
                     let tl   = tail_seg sg     in
                     B.live h cell /\
                     g_cell_next a h cell == sg_entry tl /\
                     live_seg a h tl))

inline_for_extraction
let sg_mkcons (#c : Type) (a : queue_param c) (hd : G.erased (B.pointer c)) (tl : G.erased (list_seg c))
  : Stack (G.erased (list_seg c))
          (requires fun h -> B.live h hd /\
                          g_cell_next a h hd == sg_entry tl /\
                          live_seg a h tl)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == cons_seg hd tl /\
                          live_seg a h sg)
  = let h = ST.get () in sg_mkcons_lem a h hd tl;
    cons_seg hd tl

inline_for_extraction
let sg_mksglt (#c : Type) (a : queue_param c) (hd : G.erased (B.pointer c)) (exit : G.erased (cell_ptr c))
  : Stack (G.erased (list_seg c))
          (requires fun h -> B.live h hd /\
                          g_cell_next a h hd == G.reveal exit)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == { segment = [G.reveal hd]; exit } /\
                          live_seg a h sg)
  = sg_mkcons a hd (empty_seg exit)

inline_for_extraction
let sg_mkapp (#c : Type) (a : queue_param c) (sg0 sg1 : G.erased (list_seg c))
  : Stack (G.erased (list_seg c))
          (requires fun h -> live_seg a h sg0 /\ live_seg a h sg1 /\
                          sg0.exit == sg_entry sg1)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == append_seg sg0 sg1 /\
                          live_seg a h sg)
  = let h = ST.get () in append_seg_live a h sg0 sg1;
    append_seg sg0 sg1


inline_for_extraction
let sg_uncons (#c : Type) (a : queue_param c) (sg : G.erased (list_seg c))
  : Stack (G.erased (B.pointer c) & G.erased (list_seg c))
          (requires fun h -> live_seg a h sg /\ Cons? sg.segment)
          (ensures  fun h (cell, tl) h' -> h' == h /\
                     G.reveal sg == cons_seg cell tl /\
                     G.reveal tl == tail_seg sg /\
                     B.live h cell /\
                     g_cell_next a h cell == sg_entry tl /\
                     live_seg a h tl)
  =
    let h = ST.get () in sg_uncons_lem a h sg;
    G.hide (L.hd sg.segment),
    G.hide (tail_seg sg)

inline_for_extraction
let sg_unapp (#c : Type) (a : queue_param c) (sg0 sg1 : G.erased (list_seg c))
  : Stack  unit
          (requires fun h -> live_seg a h (append_seg sg0 sg1) /\
                          sg0.exit == sg_entry sg1)
          (ensures  fun h () h' -> h' == h /\
                          live_seg a h sg0 /\ live_seg a h sg1)
  = let h = ST.get () in append_seg_live a h sg0 sg1

val entry_null_is_empty (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_seg c)
  : Lemma (requires live_seg a h sg /\ B.g_is_null (sg_entry sg))
          (ensures  sg == empty_list c)
          [SMTPat (live_seg a h sg)]

val list_nil_entry_nnull (#c : Type) (a : queue_param c) (h : HS.mem) (sg : list_nil c)
  : Lemma (requires live_seg a h sg /\ not (B.g_is_null (sg_entry sg)))
          (ensures  Cons? sg.segment)
          [SMTPat (live_seg a h sg); SMTPat (Cons? sg.segment)]

inline_for_extraction
val sgn_entry (#c : Type) (a : queue_param c) (p : cell_ptr c) (sg : G.erased (list_nil c))
  : Stack (cell_ptr c)
                (requires fun h0       -> live_seg a h0 sg /\ p == sg_entry sg)
                (ensures  fun h0 p' h1 -> h0 == h1 /\ B.live h1 p /\ p' == p)

inline_for_extraction
let sg_last (#c : Type) (a : queue_param c) (p : cell_ptr c) (sg : G.erased (list_nil c))
  : Stack (cell_ptr c)
                (requires fun h0       -> live_seg a h0 sg /\ p == last_cell sg.segment)
                (ensures  fun h0 p' h1 -> h0 == h1 /\ B.live h1 p /\ p' == p)
  = let h = ST.get () in last_cell_live a h sg;
    p

inline_for_extraction
val sg_next (#c : Type) (a : queue_param c)
            (p : cell_ptr c) (sg : G.erased (list_seg c))
  : Stack (cell_ptr c)
          (requires fun h0       -> live_seg a h0 sg /\ p == sg_entry sg /\ Cons? sg.segment)
          (ensures  fun h0 p' h1 -> h0 == h1 /\
                                 live_seg a h1 (tail_seg sg) /\ p' == sg_entry (tail_seg sg))

(** Lemmas *)

let rec unsnoc_seg (#c : Type) (sg : list_seg c)
  : Pure (list_seg c & list_seg c)
         (requires Cons? sg.segment)
         (ensures fun (ini, lt) ->
                   lt == { segment = [last_cell sg.segment]; exit = sg.exit } /\
                   sg == append_seg ini lt /\
                   ini.exit == last_cell sg.segment)
         (decreases sg.segment)
  = match sg.segment with
    | [lt]   -> empty_seg lt, sg
    | hd :: _ -> let ini, lt = unsnoc_seg (tail_seg sg) in
               cons_seg hd ini, lt

let rec append_last_cell (#c : Type) (sg0 sg1 : list (B.pointer c))
  : Lemma (requires  Cons? sg1)
          (ensures   last_cell L.(sg0@sg1) == last_cell sg1)
          (decreases sg0)
  = match sg0 with
    | [] -> () | _ :: tl -> append_last_cell tl sg1
