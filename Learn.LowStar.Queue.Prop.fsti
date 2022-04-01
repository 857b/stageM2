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

open Learn.LowStar.Queue.Data


let g_cell_next (#a : Type) (h : HS.mem) (p : B.pointer (cell a)) : GTot (cell_ptr a)
  = (B.deref h p).next

(** Ghost representation of the structures *)

noextract noeq
type list_seg (a : Type) = {
  segment : list (B.pointer (cell a));
  exit    : cell_ptr a
}

let list_nil (a : Type) : Type = sg:list_seg a{sg.exit == B.null}

type cell_list (a : Type) = list (B.pointer (cell a))

let sg_of_cells (#a : Type) (l : cell_list a) : list_nil a
  = { segment = l; exit = B.null }


let sg_entry (#a : Type) (sg : list_seg a) : Tot (cell_ptr a)
  = match sg.segment with
    | []    -> sg.exit
    | hd :: _ -> hd

let cons_seg (#a : Type) (hd : B.pointer (cell a)) (sg : list_seg a) : list_seg a
  = { sg with segment = hd :: sg.segment }

let tail_seg (#a : Type) (sg : list_seg a)
  : Pure (list_seg a) (requires Cons? sg.segment) (ensures fun _ -> True)
  = {sg with segment = L.tail sg.segment}

let append_seg (#a : Type) (sg0 sg1 : list_seg a) : Tot (list_seg a)
  = { segment = L.(sg0.segment @ sg1.segment);
      exit    = sg1.exit }

let append_seg_assoc (#a : Type) (sg0 sg1 sg2 : list_seg a)
  : Lemma (ensures append_seg sg0 (append_seg sg1 sg2) == append_seg (append_seg sg0 sg1) sg2)
  = L.append_assoc sg0.segment sg1.segment sg2.segment

let rec last_cell (#a : Type) (sg : cell_list a)
  : Pure (cell_ptr a)
         (requires True)
         (ensures fun lt -> B.g_is_null lt <==> Nil? sg)
         (decreases sg)
  = match sg with
    | []     -> B.null
    | [c]    -> c
    | _ :: tl -> last_cell tl


(** Predicates *)

let rec loc_seg (#a : Type) (sg : cell_list a) : GTot M.loc
  (decreases sg)
  = match sg with
    | [] -> M.loc_none
    | hd :: tl -> M.(loc_union (loc_buffer hd) (loc_seg tl))

let rec wf_seg (#a : Type) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> (M.loc_disjoint (B.loc_buffer hd) (loc_seg tl))
             /\ wf_seg (tail_seg sg)

let rec live_seg_def (#a : Type) (h : HS.mem) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: _ -> let sg' = tail_seg sg in
               B.live h hd /\ g_cell_next h hd == sg_entry sg' /\ live_seg_def h sg'

(* ALT? [@@"opaque_to_smt"] + reveal_opaque *)
val live_seg (#a : Type) (h : HS.mem) (sg : list_seg a) : Tot prop

val live_seg_unfold : a:Type -> Lemma (live_seg #a == live_seg_def #a)


/// A queue is a [queue_st] with a linked list of [cell].
///   The first element of the list is the older element.
///   - [q_exit] points to the entry of the list.
///   - [q_entry] points to the last element of the list (or null if the queue is empty)
///     ALT? unspecified if the queue is empty

let loc_queue (#a : Type) (q : queue a) (l : cell_list a) : GTot M.loc =
  M.(loc_union (loc_buffer q) (loc_seg l))

let wf_queue (#a : Type) (q : queue a) (l : cell_list a) : Tot prop =
  wf_seg (sg_of_cells l) /\ M.(loc_disjoint (loc_buffer q) (loc_seg l))

let live_queue (#a : Type) (h : HS.mem) (q : queue a) (l : cell_list a) : Tot prop =
  B.live h q /\ live_seg h (sg_of_cells l) /\
 (let qs = B.deref h q in
  qs.q_exit  == sg_entry (sg_of_cells l) /\
  qs.q_entry == last_cell l)

let mod_next (#a : Type) (h0 h1 : HS.mem) (c : B.pointer (cell a)) : GTot prop
  = B.live h0 c /\ B.live h1 c /\ (B.deref h0 c).data == (B.deref h1 c).data

let mod_next_list (#a : Type) (h0 h1 : HS.mem) (cs : cell_list a)
  : GTot prop
  = Ll.g_for_allP cs (mod_next #a h0 h1)


(** Lemmas about the predicates *)

val loc_seg_live_in (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg) (ensures B.loc_in (loc_seg sg.segment) h)
          (decreases sg.segment)
    [SMTPat (live_seg h sg)]

val frame_seg (#a : Type) (h0 h1 : HS.mem) (sg : list_seg a) (r : B.loc)
  : Lemma (requires live_seg h0 sg /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_seg sg.segment)))
          (ensures  live_seg h1 sg)
          (decreases sg.segment)
    [SMTPat (live_seg #a h0 sg); SMTPat (M.modifies r h0 h1)]


let disjoint_mod_next (#a : Type) (h0 h1 : HS.mem) (p : M.loc) (c : B.pointer (cell a))
  : Lemma (requires M.(loc_disjoint (loc_buffer c) p /\ live h0 c /\ modifies p h0 h1))
          (ensures  mod_next h0 h1 c)
  = ()

val disjoint_mod_next_seg (#a : Type) (h0 h1 : HS.mem) (p : M.loc) (sg : list_seg a)
  : Lemma (requires  M.(loc_disjoint (loc_seg sg.segment) p /\
                        live_seg h0 sg /\ modifies p h0 h1))
          (ensures   mod_next_list h0 h1 sg.segment)
          (decreases sg.segment)



let rec append_seg_loc (#a : Type) (sg0 sg1 : cell_list a)
  : Lemma (ensures loc_seg L.(sg0@sg1) == M.loc_union (loc_seg sg0) (loc_seg sg1))
          (decreases sg0)
          [SMTPat (loc_seg L.(sg0@sg1))]
  = match sg0 with
    | [] -> ()
    | hd :: tl ->
      append_seg_loc tl sg1;
      M.loc_union_assoc (M.loc_buffer hd) (loc_seg tl) (loc_seg sg1)

let rec append_seg_wf (#a : Type) (sg0 sg1 : list_seg a)
  : Lemma (ensures wf_seg (append_seg sg0 sg1) <==>
                   wf_seg sg0 /\ wf_seg sg1 /\ M.loc_disjoint (loc_seg sg0.segment) (loc_seg sg1.segment))
          (decreases sg0.segment)
          [SMTPat (wf_seg (append_seg sg0 sg1))]
  = match sg0.segment with
    | [] -> ()
    | _ :: _ -> append_seg_wf (tail_seg sg0) sg1

val append_seg_live (#a : Type) (h : HS.mem) (sg0 sg1 : list_seg a)
  : Lemma (requires sg0.exit == sg_entry sg1)
          (ensures live_seg h (append_seg sg0 sg1) <==> live_seg h sg0 /\ live_seg h sg1)
          (decreases sg0.segment)

val last_cell_live (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg)
          (ensures B.live h (last_cell sg.segment))
          (decreases sg.segment)

(** Segments handling *)

noextract let empty_seg  (#a : Type) (exit : cell_ptr a) = { segment = []; exit }
noextract let empty_list (a : Type) : list_nil a = empty_seg B.null
val empty_live (#a : Type) (exit : B.pointer_or_null (cell a)) (h : HS.mem)
  : Lemma (live_seg h (empty_seg #a exit)) [SMTPat (live_seg h (empty_seg #a exit))]

let empty_sg_of_cell (#a : Type)
  : Lemma (sg_of_cells #a [] == empty_list a) [SMTPat (sg_of_cells #a [])]
  = ()

val sg_mkcons_lem (#a : Type) (h : HS.mem) (hd : B.pointer (cell a)) (tl : list_seg a)
  : Lemma (requires B.live h hd /\
                    g_cell_next h hd == sg_entry tl /\
                    live_seg h tl)
          (ensures  live_seg h (cons_seg hd tl))

val sg_uncons_lem (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ Cons? sg.segment)
          (ensures  (let cell = L.hd sg.segment in
                     let tl   = tail_seg sg     in
                     B.live h cell /\
                     g_cell_next h cell == sg_entry tl /\
                     live_seg h tl))

inline_for_extraction
let sg_mkcons (#a : Type) (hd : G.erased (B.pointer (cell a))) (tl : G.erased (list_seg a))
  : Stack (G.erased (list_seg a))
          (requires fun h -> B.live h hd /\
                          g_cell_next h hd == sg_entry tl /\
                          live_seg h tl)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == cons_seg hd tl /\
                          live_seg h sg)
  = let h = ST.get () in sg_mkcons_lem h hd tl;
    cons_seg hd tl

inline_for_extraction
let sg_mksglt (#a : Type) (hd : G.erased (B.pointer (cell a))) (exit : G.erased (cell_ptr a))
  : Stack (G.erased (list_seg a))
          (requires fun h -> B.live h hd /\
                          g_cell_next h hd == G.reveal exit)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == { segment = [G.reveal hd]; exit } /\
                          live_seg h sg)
  = sg_mkcons hd (empty_seg exit)

inline_for_extraction
let sg_mkapp (#a : Type) (sg0 sg1 : G.erased (list_seg a))
  : Stack (G.erased (list_seg a))
          (requires fun h -> live_seg h sg0 /\ live_seg h sg1 /\
                          sg0.exit == sg_entry sg1)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == append_seg sg0 sg1 /\
                          live_seg h sg)
  = let h = ST.get () in append_seg_live h sg0 sg1;
    append_seg sg0 sg1


inline_for_extraction
let sg_uncons (#a : Type) (sg : G.erased (list_seg a))
  : Stack (G.erased (B.pointer (cell a)) & G.erased (list_seg a))
          (requires fun h -> live_seg h sg /\ Cons? sg.segment)
          (ensures  fun h (cell, tl) h' -> h' == h /\
                     G.reveal sg == cons_seg cell tl /\
                     G.reveal tl == tail_seg sg /\
                     B.live h cell /\
                     g_cell_next h cell == sg_entry tl /\
                     live_seg h tl)
  =
    let h = ST.get () in sg_uncons_lem h sg;
    G.hide (L.hd sg.segment),
    G.hide (tail_seg sg)

inline_for_extraction
let sg_unapp (#a : Type) (sg0 sg1 : G.erased (list_seg a))
  : Stack  unit
          (requires fun h -> live_seg h (append_seg sg0 sg1) /\
                          sg0.exit == sg_entry sg1)
          (ensures  fun h () h' -> h' == h /\
                          live_seg h sg0 /\ live_seg h sg1)
  = let h = ST.get () in append_seg_live h sg0 sg1

val entry_null_is_empty (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ B.g_is_null (sg_entry sg))
          (ensures  sg == empty_list a)
          [SMTPat (live_seg h sg)]

val list_nil_entry_nnull (#a : Type) (h : HS.mem) (sg : list_nil a)
  : Lemma (requires live_seg h sg /\ not (B.g_is_null (sg_entry sg)))
          (ensures  Cons? sg.segment)
          [SMTPat (live_seg h sg); SMTPat (Cons? sg.segment)]

inline_for_extraction
val sgn_entry (#a : Type) (p : cell_ptr a) (sg : G.erased (list_nil a))
  : Stack (cell_ptr a)
                (requires fun h0       -> live_seg h0 sg /\ p == sg_entry sg)
                (ensures  fun h0 p' h1 -> h0 == h1 /\ B.live h1 p /\ p' == p)

inline_for_extraction
let sg_last (#a : Type) (p : cell_ptr a) (sg : G.erased (list_nil a))
  : Stack (cell_ptr a)
                (requires fun h0       -> live_seg h0 sg /\ p == last_cell sg.segment)
                (ensures  fun h0 p' h1 -> h0 == h1 /\ B.live h1 p /\ p' == p)
  = let h = ST.get () in last_cell_live h sg;
    p

inline_for_extraction
val sg_next (#a : Type) (p : cell_ptr a) (sg : G.erased (list_seg a))
  : Stack (cell_ptr a)
          (requires fun h0       -> live_seg h0 sg /\ p == sg_entry sg /\ Cons? sg.segment)
          (ensures  fun h0 p' h1 -> h0 == h1 /\
                                 live_seg h1 (tail_seg sg) /\ p' == sg_entry (tail_seg sg))

(** Lemmas *)

let rec unsnoc_seg (#a : Type) (sg : list_seg a)
  : Pure (list_seg a & list_seg a)
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

let rec append_last_cell (#a : Type) (sg0 sg1 : list (B.pointer (cell a)))
  : Lemma (requires  Cons? sg1)
          (ensures   last_cell L.(sg0@sg1) == last_cell sg1)
          (decreases sg0)
  = match sg0 with
    | [] -> () | _ :: tl -> append_last_cell tl sg1
