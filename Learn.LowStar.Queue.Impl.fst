module Learn.LowStar.Queue.Impl

module U   = Learn.Util
module L   = FStar.List.Pure
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LLoops = Learn.LowStar.Loops

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
                                loc_includes (loc_region_only true r) (loc_buffer q) /\
                                freeable q) /\
                             live_queue h1 q [])
  =
    B.malloc #(queue_st a) r ({q_exit = B.null; q_entry = B.null}) 1ul

(* [free] *)

let free (#a : Type) (q : queue a)
  : ST  unit
       (requires fun h      -> live_queue h q [] /\ M.freeable q)
       (ensures  fun h b h' -> M.(modifies (loc_addr_of_buffer q) h h'))
  =
    B.free q

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
        let tl = (sg_uncons tls)._1 in
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

let dequeue (#a : Type) (q : queue a) (l : G.erased (cell_list a))
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

(* [find] *)

#push-options "--ifuel 1"
let rec find_gtot (#a:Type) (f:a -> GTot bool) (l:list a) : GTot (option (x:a{f x})) (decreases l)
  = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some #(x:a{f x}) hd else find_gtot f tl
#pop-options


inline_for_extraction
let rec list_find_rec (#a : Type)
         (p : cell_ptr a) (sg : G.erased (list_nil a))
         (h0 : HS.mem) (* needed to specify [f] *)
         (spec_f : (x : B.pointer (cell a) -> GTot bool))
         (f : (x : B.pointer (cell a)) ->
              Stack bool
                    (requires fun h      -> h == h0 /\ B.live h x /\ L.memP x sg.segment)
                    (ensures  fun h b h' -> h' == h /\ b = spec_f x))
   : Stack (B.pointer_or_null (cell a))
          (requires fun h       -> h == h0 /\ live_seg h sg /\ p == sg_entry sg)
          (ensures  fun h rt h' -> h' == h /\
                                rt == (match find_gtot spec_f sg.segment with
                                       | Some p -> p | None -> B.null))
   =
     if B.is_null (sgn_entry p sg) then B.null
     else begin
         let tl = (sg_uncons (G.reveal sg))._2 in
       if f p then p
       else list_find_rec (sg_next p (G.reveal sg)) (G.reveal tl) h0 spec_f f
     end

#push-options "--z3rlimit 20"
inline_for_extraction
let list_find_loop (#a : Type)
         (p : cell_ptr a) (sg0 : G.erased (list_nil a))
         (h0  : HS.mem)
         (spec_f : (x : B.pointer (cell a) -> GTot bool))
         (f : (x : B.pointer (cell a)) ->
              Stack bool
                    (requires fun h -> M.(modifies loc_none h0 h) /\ B.live h x /\ L.memP x sg0.segment)
                    (ensures  fun h b h' -> M.(modifies loc_none h h') /\ b = spec_f x))
   : Stack (B.pointer_or_null (cell a))
          (requires fun h       -> h == h0 /\ live_seg h sg0 /\ p == sg_entry sg0)
          (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                                rt == (match find_gtot spec_f sg0.segment with
                                       | Some p -> p | None -> B.null))
   =
     push_frame ();
       let h0' = ST.get () in
     let it = B.alloca #(cell_ptr a & G.erased (list_nil a)) (p, sg0) 1ul in
     let rt = B.alloca #(cell_ptr a) B.null 1ul in
       let lloc = G.hide (M.(loc_union (loc_buffer it) (loc_buffer rt))) in
     let pre h1 : prop =
         M.(let (p, sg) = deref h1 it in
         modifies loc_none h0 h1 /\
         live h1 it /\ live h1 rt /\
         live_seg h1 (deref h1 it)._2 /\
         loc_disjoint (loc_buffer it) (loc_seg sg.segment) /\
         p == sg_entry sg /\
         (forall x . {:pattern (L.memP x sg0.segment)} L.memP x sg.segment ==> L.memP x sg0.segment))
     in let post_test h1 (b:bool) : prop =
         (Cons? (B.deref h1 it)._2.segment <==> b)
     in let post h1 (x : cell_ptr a) h2 : prop =
         let _,sg = B.deref h1 it in
         let dflt = B.deref h1 rt in
         M.(modifies lloc h1 h2) /\
         x == (match find_gtot spec_f sg.segment with
                     | Some p -> p | None -> dflt)
     in
     let test () : Stack bool
              (requires fun h1       -> pre h1)
              (ensures  fun h1 b h1' -> h1' == h1 /\ post_test h1 b)
       =   let sg = (it.(0ul))._2 in
         not (B.is_null (sgn_entry (it.(0ul))._1 sg))
     in
     let body () : Stack unit
              (requires fun h1       -> pre h1 /\ Cons? (B.deref h1 it)._2.segment)
              (ensures  fun h1 () h2 -> pre h2 /\
                                     LLoops.tail_rec_post h2 (post h2) (post h1))
       =   let h1 = ST.get () in
           let sg = (it.(0ul))._2 in
           let tl = (sg_uncons (G.reveal sg))._2 in
         if f (sgn_entry (it.(0ul))._1 sg)
         then begin
           rt.(0ul) <- (it.(0ul))._1;
           it.(0ul) <- (B.null, G.hide (empty_list a))
         end else begin
           it.(0ul) <- (sg_next (it.(0ul))._1 (G.hide (G.reveal sg)), (G.hide (G.reveal tl)))
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
let find (#a : Type)
         (q : queue a) (l : G.erased (cell_list a))
         (h0  : HS.mem)
         (spec_f : (x : B.pointer (cell a) -> GTot bool))
         (f : (x : B.pointer (cell a)) ->
              Stack bool
                    (requires fun h -> M.(modifies loc_none h0 h) /\ B.live h x /\ L.memP x l)
                    (ensures  fun h b h' -> M.(modifies loc_none h h') /\ b = spec_f x))
  : Stack (B.pointer_or_null (cell a))
          (requires fun h       -> h == h0 /\ live_queue h q l)
          (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                                rt == (match find_gtot spec_f l with
                                       | Some p -> p | None -> B.null))
  = list_find_loop ((q.(0ul)).q_exit) (sg_of_cells l) h0 spec_f f
 
(* ---------- *)

let malloc_u32   = malloc    U32.t
let is_empty_u32 = is_empty #U32.t
let enqueue_u32  = enqueue  #U32.t
let dequeue_u32  = dequeue  #U32.t

let mem_42 (q : queue U32.t) (l : G.erased (cell_list U32.t))
  : Stack (B.pointer_or_null (cell U32.t))
          (requires fun h       -> live_queue h q l)
          (ensures  fun h rt h' -> M.(modifies loc_none h h') /\
                    rt == (match find_gtot (fun (c:B.pointer (cell U32.t)) -> (B.deref h c).data = 42ul) l with
                           | Some p -> p | None -> B.null))
  =   let h = ST.get () in
    find q l h (fun c -> (B.deref h c).data = 42ul)
               (fun c -> live_seg_cell h (sg_of_cells l) c; (c.(0ul)).data = 42ul)

#push-options "--fuel 3 --z3rlimit 40"
let test_queue_spec () : St unit
  =
    push_frame ();
    let q = malloc U32.t HS.root in
    let x0 = B.malloc #(cell U32.t) HS.root ({data = 5ul; next = B.null}) 1ul in
    enqueue x0 q [];
      (let h = ST.get () in assert (live_queue h q [x0]));
      (let d = (x0.(0ul)).data in assert (d == 5ul));
      (let f = mem_42 q [x0] in assert (f == B.null));
      (let h0 = ST.get () in
    x0.(0ul) <- {x0.(0ul) with data = 42ul};
      (let h1 = ST.get () in
       frame_seg_mod_data h0 h1 (sg_of_cells [x0]);
       assert (live_queue h1 q [x0])));
      (let f = mem_42 q [x0] in assert (f == x0));

    let x12 = B.alloca #(cell U32.t) ({data = 7ul; next = B.null}) 2ul in
    let x1 = B.sub x12 0ul 1ul in let x2 = B.sub x12 1ul 1ul in
    enqueue x1 q [x0];
      (let h0 = ST.get () in assert (live_queue h0 q [x0; x1]);
    x2.(0ul) <- {x2.(0ul) with data = 8ul};
      let h1 = ST.get () in
      frame_seg h0 h1 (sg_of_cells [x0; x1]) (M.loc_buffer x2);
      assert (live_queue h1 q [x0; x1]));
    let x0' = dequeue q [x0; x1] in
      assert (x0' == x0);
    B.free x0;
    let x1' = dequeue q [x1] in
      (assert (x1' == x1); let d = (x1.(0ul)).data in assert (d = 7ul));
    pop_frame ();
    free q
#pop-options
