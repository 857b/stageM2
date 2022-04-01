module Learn.LowStar.Queue.Impl

module U   = Learn.Util
module L   = FStar.List.Pure
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module U32 = FStar.UInt32

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.Queue.Data
open Learn.LowStar.Queue.Prop

#set-options "--fuel 2 --ifuel 0"

(* [malloc] *)

let malloc (a : Type) (r : HS.rid)
  : ST (queue a)
       (requires fun _       -> ST.is_eternal_region r)
       (ensures  fun h0 q h1 -> M.(modifies loc_none h0 h1 /\
                                fresh_loc (loc_buffer q) h0 h1 /\
                                loc_includes (loc_region_only true r) (loc_buffer q)) /\
                             live_queue h1 q [])
  =
    B.malloc #(queue_st a) r ({q_exit = B.null; q_entry = B.null}) 1ul

(* [is_empty] *)

let is_empty (#a : Type) (x : B.pointer (cell a)) (q : queue a) (l : G.erased (cell_list a))
  : Stack  bool
          (requires fun h      -> live_queue h q l)
          (ensures  fun h b h' -> h' == h /\ b = Nil? l)
  = B.is_null (sgn_entry (q.(0ul)).q_exit (sg_of_cells l))

(* [enqueue] *)

let enqueue (#a : Type) (x : B.pointer (cell a)) (q : queue a) (l : G.erased (cell_list a))
  : Stack  unit
          (requires fun h0       -> wf_queue q l /\ live_queue h0 q l /\
                                 B.live h0 x /\
                                 M.(loc_disjoint (loc_buffer x) (loc_queue q l)))
          (ensures  fun h0 () h1 -> M.(modifies (loc_union (loc_buffer x) (loc_queue q l)) h0 h1) /\
                                 mod_next h0 h1 x /\ mod_next_list h0 h1 l /\
                                 live_queue h1 q (L.snoc (G.reveal l,x)))
  =   
      let h0 = ST.get () in
      let sg = G.hide (sg_of_cells l) in
    x.(0ul) <- {x.(0ul) with next = B.null};
    if B.is_null (sg_last (q.(0ul)).q_entry sg) then begin
      q.(0ul) <- {q_exit = x; q_entry = x};
        let _ = sg_mksglt x B.null in ()
    end else begin
        let ini = G.hide (unsnoc_seg sg)._1 in
        let tls = G.hide (unsnoc_seg sg)._2 in
        sg_unapp ini tls;
        let tl,_ = sg_uncons tls in
        assert (loc_seg tls.segment == B.loc_buffer tl);
        assert (loc_seg sg.segment  == M.(loc_union (loc_seg ini.segment) (B.loc_buffer tl)));
      (q.(0ul)).q_entry.(0ul) <- {(q.(0ul)).q_entry.(0ul) with next = x};
      q.(0ul) <- {q.(0ul) with q_entry = x};
        let h1 = ST.get () in
        let sg' = sg_mkapp ini (sg_mkcons tl (sg_mksglt x B.null)) in
        L.append_assoc (ini.segment) [G.reveal tl] [x];
        assert (L.snoc (G.reveal l,x) == sg'.segment);
        append_last_cell sg.segment [x];
        assert (sg_entry sg' == sg_entry sg);
        U.assert_by (mod_next_list h0 h1 l) (fun () ->
          append_seg_live h0 ini tls;
          sg_uncons_lem h0 tls;
          let md = M.(loc_union (loc_buffer x) (loc_union (loc_buffer tl) (loc_buffer q))) in
          disjoint_mod_next_seg h0 h1 md ini;
          assert (mod_next_list h0 h1 [G.reveal tl]))
    end

(* [dequeue] *)

let dequeue (#a : Type) (x : B.pointer (cell a)) (q : queue a) (l : G.erased (cell_list a))
  : Stack (B.pointer (cell a))
          (requires fun h0       -> wf_queue q l /\ live_queue h0 q l /\
                                 Cons? l)
          (ensures  fun h0 rt h1 -> M.modifies (loc_queue q l) h0 h1 /\
                                 mod_next_list h0 h1 l /\
                                 rt == L.hd l /\
                                 live_queue h1 q (L.tl l) /\ B.live h1 rt)
  =
      let h0 = ST.get () in
      let sg = G.hide (sg_of_cells l) in
      let hd,sg' = sg_uncons sg in
    let rt = (q.(0ul)).q_exit in
    q.(0ul) <- { q.(0ul) with q_exit = sg_next rt sg };
    if B.is_null (sgn_entry (q.(0ul)).q_exit (G.reveal sg')) then
      q.(0ul) <- { q.(0ul) with q_entry = B.null };
      let h1 = ST.get () in G.hide(
      let md = M.(loc_union (loc_buffer hd) (loc_buffer q)) in
      disjoint_mod_next_seg h0 h1 md sg');
    rt


(* ---------- *)

let malloc_u32   = malloc    U32.t
let is_empty_u32 = is_empty #U32.t
let enqueue_u32  = enqueue  #U32.t
let dequeue_u32  = dequeue  #U32.t
