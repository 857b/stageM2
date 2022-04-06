module Learn.LowStar.Queue

include Learn.LowStar.Queue.Param

module L   = FStar.List.Pure
module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module HS  = FStar.HyperStack
module G   = FStar.Ghost
open FStar.HyperStack.ST


val queue (c : Type0) : Type0

(* Ghost properties *)

val loc_queue_st    (#c : Type) (q : queue c) : GTot M.loc

val loc_queue       (#c : Type) (q : queue c) (l : cell_list c) : GTot M.loc

val wf_queue        (#c : Type) (q : queue c) (l : cell_list c) : Tot prop

val live_queue      (#c : Type) (a : queue_param c) (h : HS.mem) (q : queue c) (l : cell_list c) : Tot prop

val freeable        (#c : Type) (q : queue c) : Tot prop

(* Functions *)

noextract inline_for_extraction
val malloc (#c : Type) (a : queue_param c) (r : HS.rid)
  : ST (queue c)
       (requires fun _       -> is_eternal_region r)
       (ensures  fun h0 q h1 -> M.(modifies loc_none h0 h1 /\
                                fresh_loc (loc_queue_st q) h0 h1 /\
                                loc_includes (loc_region_only true r) (loc_queue_st q)) /\
                             freeable q /\
                             wf_queue q [] /\ loc_queue q [] == loc_queue_st q /\ live_queue a h1 q [])

noextract inline_for_extraction
val free (#c : Type) (a : queue_param c) (q : queue c)
  : ST  unit
       (requires fun h      -> live_queue a h q [] /\ freeable q)
       (ensures  fun h b h' -> M.(modifies (loc_queue_st q) h h'))

noextract inline_for_extraction
val is_empty (#c : Type) (a : queue_param c) (q : queue c) (l : G.erased (cell_list c))
  : Stack  bool
          (requires fun h      -> live_queue a h q l)
          (ensures  fun h b h' -> h' == h /\ b = Nil? l)

noextract inline_for_extraction
val enqueue (#c : Type) (a : queue_param c)
            (x : B.pointer c) (q : queue c) (l : G.erased (cell_list c))
  : Stack  unit
          (requires fun h0       -> wf_queue q l /\ live_queue a h0 q l /\
                                 B.live h0 x /\
                                 M.(loc_disjoint (loc_buffer x) (loc_queue q l)))
          (ensures  fun h0 () h1 -> M.(modifies (loc_union (loc_queue q l) (loc_buffer x)) h0 h1) /\
                                 mod_next a h0 h1 x /\ mod_next_list a h0 h1 l /\
                                (let l' = L.snoc (G.reveal l,x) in
                                 wf_queue q l' /\
                                 live_queue a h1 q l' /\
                                 M.(loc_queue q l' == loc_union (loc_queue q l) (loc_buffer x))))

noextract inline_for_extraction
val dequeue (#c : Type) (a : queue_param c)
            (q : queue c) (l : G.erased (cell_list c))
  : Stack (B.pointer c)
          (requires fun h0       -> wf_queue q l /\ live_queue a h0 q l /\
                                 Cons? l)
          (ensures  fun h0 rt h1 -> M.modifies (loc_queue q l) h0 h1 /\
                                 mod_next_list a h0 h1 l /\
                                 rt == L.hd l /\
                                (let l' = L.tl l in
                                 wf_queue q l' /\
                                 live_queue a h1 q (L.tl l) /\ B.live h1 rt /\
                                 M.(loc_queue q l == loc_union (loc_buffer rt) (loc_queue q l') /\
                                    loc_disjoint (loc_buffer rt) (loc_queue q l'))))

noextract inline_for_extraction
val find (#c : Type) (a : queue_param c)
         (q : queue c) (l : G.erased (cell_list c))
         (h0  : HS.mem)
         (spec_f : (x : B.pointer c -> GTot bool))
         (f : (x : B.pointer c) ->
              Stack bool
                    (requires fun h -> M.(modifies loc_none h0 h) /\ B.live h x /\ L.memP x l)
                    (ensures  fun h b h' -> M.(modifies loc_none h h') /\ b = spec_f x))
  : Stack (cell_ptr c)
          (requires fun h       -> h == h0 /\ live_queue a h q l)
          (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                                rt == (match Ll.find_gtot spec_f l with
                                       | Some p -> p | None -> B.null))

(* Lemmas *)

val loc_queue_live_in (#c : Type) (a : queue_param c) (h : HS.mem) (q : queue c) (l : cell_list c)
  : Lemma (requires live_queue a h q l)
          (ensures B.loc_in (loc_queue q l) h)
    [SMTPat (live_queue a h q l)]

val frame_queue (#c : Type) (a : queue_param c) (h0 h1 : HS.mem) (q : queue c) (l : cell_list c) (r : B.loc)
  : Lemma (requires live_queue a h0 q l /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_queue q l)))
          (ensures  live_queue a h1 q l)
    [SMTPat (live_queue a h0 q l); SMTPat (M.modifies r h0 h1)]

val frame_queue_mod_data (#c : Type) (a : queue_param c)
                         (h0 h1 : HS.mem) (q : queue c) (l : cell_list c) (r : B.loc)
  : Lemma (requires live_queue a h0 q l /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_queue_st q)) /\
                    mod_data_list a h0 h1 l)
          (ensures  live_queue a h1 q l)


val loc_queue_content (#c : Type) (q : queue c) (l : cell_list c) (x : B.pointer c)
  : Lemma (requires  L.memP x l)
          (ensures   M.(loc_queue q l `loc_includes` loc_buffer x))

val live_queue_content (#c : Type) (a : queue_param c)
                       (h : HS.mem) (q : queue c) (l : cell_list c) (x : B.pointer c)
  : Lemma (requires  live_queue a h q l /\ L.memP x l)
          (ensures   B.live h x)

(* TODO? : loc_queue q [] = loc_queue_st q, loc =, disjoint content ... *)
