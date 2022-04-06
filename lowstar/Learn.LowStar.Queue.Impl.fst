module Learn.LowStar.Queue.Impl

module U   = Learn.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LLoops = Learn.LowStar.Loops

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.Queue.Param
open Learn.LowStar.Queue.Prop

#set-options "--fuel 2 --ifuel 0"

(* [malloc] *)

inline_for_extraction
let malloc (#c : Type) (a : queue_param c) (r : HS.rid)
  : ST (queue c)
       (requires fun _       -> ST.is_eternal_region r)
       (ensures  fun h0 q h1 -> M.(modifies loc_none h0 h1 /\
                                fresh_loc (loc_addr_of_buffer q) h0 h1 /\
                                loc_includes (loc_region_only true r) (loc_addr_of_buffer q) /\
                                freeable q) /\
                             live_queue a h1 q [])
  =
    B.malloc #(queue_st c) r ({q_exit = B.null; q_entry = B.null}) 1ul

(* [free] *)

inline_for_extraction
let free (#c : Type) (a : queue_param c) (q : queue c)
  : ST  unit
       (requires fun h      -> live_queue a h q [] /\ M.freeable q)
       (ensures  fun h b h' -> M.(modifies (loc_addr_of_buffer q) h h'))
  =
    B.free q

(* [is_empty] *)

inline_for_extraction
let is_empty (#c : Type) (a : queue_param c) (q : queue c) (l : G.erased (cell_list c))
  : Stack  bool
          (requires fun h      -> live_queue a h q l)
          (ensures  fun h b h' -> h' == h /\ b = Nil? l)
  = B.is_null (sgn_entry a (q.(0ul)).q_exit (sg_of_cells l))

(* [enqueue] *)

inline_for_extraction
let enqueue (#c : Type) (a : queue_param c)
  (x : B.pointer c) (q : queue c) (l : G.erased (cell_list c))
  : Stack  unit
          (requires fun h0       -> wf_queue q l /\ live_queue a h0 q l /\
                                 B.live h0 x /\
                                 M.(loc_disjoint (loc_buffer x) (loc_queue q l)))
          (ensures  fun h0 () h1 -> M.(modifies (loc_union (loc_buffer x) (loc_queue q l)) h0 h1) /\
                                 mod_next a h0 h1 x /\ mod_next_list a h0 h1 l /\
                                 live_queue a h1 q (L.snoc (G.reveal l,x)))
  =   
      open_queue_param a;
      let h0 = ST.get () in
      let sg = G.hide (sg_of_cells l) in
    x.(0ul) <- a.set_next (x.(0ul)) B.null;
    if B.is_null (sg_last a (q.(0ul)).q_entry sg) then begin
      q.(0ul) <- {q_exit = x; q_entry = x};
        let _ = sg_mksglt a x B.null in ()
    end else begin
        let ini = G.hide (unsnoc_seg sg)._1 in
        let tls = G.hide (unsnoc_seg sg)._2 in
        sg_unapp a ini tls;
        let tl = (sg_uncons a tls)._1 in
        assert (loc_seg tls.segment == B.loc_buffer tl);
        assert (loc_seg sg.segment  == M.(loc_union (loc_seg ini.segment) (B.loc_buffer tl)));
      (q.(0ul)).q_entry.(0ul) <- a.set_next (q.(0ul)).q_entry.(0ul) x;
      q.(0ul) <- {q.(0ul) with q_entry = x};
        let h1 = ST.get () in
        let sg' = sg_mkapp a ini (sg_mkcons a tl (sg_mksglt a x B.null)) in
        L.append_assoc (ini.segment) [G.reveal tl] [x];
        assert (L.snoc (G.reveal l,x) == sg'.segment);
        append_last_cell sg.segment [x];
        assert (sg_entry sg' == sg_entry sg);
        U.assert_by (mod_next_list a h0 h1 l) (fun () ->
          append_seg_live a h0 ini tls;
          sg_uncons_lem a h0 tls;
          let md = M.(loc_union (loc_buffer x) (loc_union (loc_buffer tl) (loc_buffer q))) in
          disjoint_mod_next_seg a h0 h1 md ini;
          assert (mod_next_list a h0 h1 [G.reveal tl]))
    end

(* [dequeue] *)

inline_for_extraction
let dequeue (#c : Type) (a : queue_param c)
            (q : queue c) (l : G.erased (cell_list c))
  : Stack (B.pointer c)
          (requires fun h0       -> wf_queue q l /\ live_queue a h0 q l /\
                                 Cons? l)
          (ensures  fun h0 rt h1 -> M.modifies (loc_queue q l) h0 h1 /\
                                 mod_next_list a h0 h1 l /\
                                 rt == L.hd l /\
                                 live_queue a h1 q (L.tl l) /\ B.live h1 rt)
  =
      open_queue_param a;
      let h0 = ST.get () in
      let sg = G.hide (sg_of_cells l) in
      let hd,sg' = sg_uncons a sg in
    let rt = (q.(0ul)).q_exit in
    q.(0ul) <- { q.(0ul) with q_exit = sg_next a rt sg };
    if B.is_null (sgn_entry a (q.(0ul)).q_exit (G.reveal sg')) then
      q.(0ul) <- { q.(0ul) with q_entry = B.null };
      let h1 = ST.get () in G.hide(
      let md = M.(loc_union (loc_buffer hd) (loc_buffer q)) in
      disjoint_mod_next_seg a h0 h1 md sg');
    rt

(* [find] *)

inline_for_extraction
let rec list_find_rec (#c : Type) (a : queue_param c)
         (p : cell_ptr c) (sg : G.erased (list_nil c))
         (h0 : HS.mem) (* needed to specify [f] *)
         (spec_f : (x : B.pointer c -> GTot bool))
         (f : (x : B.pointer c) ->
              Stack bool
                    (requires fun h      -> h == h0 /\ B.live h x /\ L.memP x sg.segment)
                    (ensures  fun h b h' -> h' == h /\ b = spec_f x))
   : Stack (cell_ptr c)
           (requires fun h       -> h == h0 /\ live_seg a h sg /\ p == sg_entry sg)
           (ensures  fun h rt h' -> h' == h /\
                                 rt == (match Ll.find_gtot spec_f sg.segment with
                                        | Some p -> p | None -> B.null))
   =
     if B.is_null (sgn_entry a p sg) then B.null
     else begin
         let tl = (sg_uncons a (G.reveal sg))._2 in
       if f p then p
       else list_find_rec a (sg_next a p (G.reveal sg)) (G.reveal tl) h0 spec_f f
     end

[@@"opaque_to_smt"]
unfold
let all_disjoint_live (h:HS.mem) (l:list M.buf_t) : prop =
  BigOps.big_and #M.buf_t (fun (|_,_,_, b|) -> M.live h b) l /\
  BigOps.pairwise_and #M.buf_t (fun (|_,_,_, b|) (|_,_,_, b'|) ->
                                  M.(loc_disjoint (loc_buffer b) (loc_buffer b'))) l

#push-options "--z3rlimit 20"
inline_for_extraction
let list_find_loop (#c : Type) (a : queue_param c)
         (p : cell_ptr c) (sg0 : G.erased (list_nil c))
         (h0  : HS.mem)
         (spec_f : (x : B.pointer c -> GTot bool))
         (f : (x : B.pointer c) ->
              Stack bool
                    (requires fun h -> M.(modifies loc_none h0 h) /\ B.live h x /\ L.memP x sg0.segment)
                    (ensures  fun h b h' -> M.(modifies loc_none h h') /\ b = spec_f x))
   : Stack (cell_ptr c)
           (requires fun h       -> h == h0 /\ live_seg a h sg0 /\ p == sg_entry sg0)
           (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                                 rt == (match Ll.find_gtot spec_f sg0.segment with
                                        | Some p -> p | None -> B.null))
   =
     push_frame ();
       let h0' = ST.get () in
     let it = B.alloca #(cell_ptr c & G.erased (list_nil c)) (p, sg0) 1ul in
     let rt = B.alloca #(cell_ptr c) B.null 1ul in
       let lloc = G.hide (M.(loc_union (loc_buffer it) (loc_buffer rt))) in
     let pre h1 : prop =
         M.(let (p, sg) = deref h1 it in
         modifies loc_none h0 h1 /\
         (*all_disjoint_live h1 M.([buf it; buf rt]) /\*)
         live h1 it /\ live h1 rt /\
         live_seg a h1 (deref h1 it)._2 /\
         loc_disjoint (loc_buffer it) (loc_seg sg.segment) /\
         p == sg_entry sg /\
         (forall x . {:pattern (L.memP x sg0.segment)} L.memP x sg.segment ==> L.memP x sg0.segment))
     in let post_test h1 (b:bool) : prop =
         (Cons? (B.deref h1 it)._2.segment <==> b)
     in let post h1 (x : cell_ptr c) h2 : prop =
         let _,sg = B.deref h1 it in
         let dflt = B.deref h1 rt in
         M.(modifies lloc h1 h2) /\
         x == (match Ll.find_gtot spec_f sg.segment with
                     | Some p -> p | None -> dflt)
     in
     let test () : Stack bool
              (requires fun h1       -> pre h1)
              (ensures  fun h1 b h1' -> h1' == h1 /\ post_test h1 b)
       =   let sg = (it.(0ul))._2 in
         not (B.is_null (sgn_entry a (it.(0ul))._1 sg))
     in
     let body () : Stack unit
              (requires fun h1       -> pre h1 /\ Cons? (B.deref h1 it)._2.segment)
              (ensures  fun h1 () h2 -> pre h2 /\
                                     LLoops.tail_rec_post h2 (post h2) (post h1))
       =   let h1 = ST.get () in
           let sg = (it.(0ul))._2 in
           let tl = (sg_uncons a (G.reveal sg))._2 in
         if f (sgn_entry a (it.(0ul))._1 sg)
         then begin
           rt.(0ul) <- (it.(0ul))._1;
           it.(0ul) <- (B.null, G.hide (empty_list c))
         end else begin
           it.(0ul) <- (sg_next a (it.(0ul))._1 (G.hide (G.reveal sg)), (G.hide (G.reveal tl)))
         end;
           let h2 = ST.get () in
           assert M.(modifies lloc h0 h2);
           U.assert_by M.(modifies loc_none h0 h2) (fun () ->
               assert M.(fresh_loc (loc_union (loc_buffer it) (loc_buffer rt)) h0 h1));
           LLoops.tail_rec_postI h2 (post h2) (post h1) (fun x h3 -> ())
     in
     let rt_v = LLoops.rec_while pre post_test post  test body (fun () -> rt.(0ul)) in
     pop_frame ();
     rt_v
#pop-options

inline_for_extraction
let find (#c : Type) (a : queue_param c)
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
  = list_find_loop a ((q.(0ul)).q_exit) (sg_of_cells l) h0 spec_f f
