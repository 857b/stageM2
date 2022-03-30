module Learn.LowStar.List

module U   = Learn.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module T   = FStar.Tactics
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LLoops = Learn.LowStar.Loops

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.List.Data

#set-options "--fuel 1 --ifuel 0"
(* live_seg pose problème sans ces options *)

(* permet de forcer une preuve de [M.modifies] par transitivité *)
noextract noeq type mod_seq (#mod : M.loc) : HS.mem -> HS.mem -> Type =
  | MNil  : h : HS.mem -> mod_seq #mod h h
  | MCons : h0 : HS.mem -> #h1 : HS.mem -> #h2 : HS.mem ->
               #squash (M.modifies mod h0 h1) -> mod_seq #mod h1 h2 -> mod_seq #mod h0 h2

#push-options "--ifuel 1"
let rec mod_of_seq (mod : M.loc) (#h0 #h1 : HS.mem) (sq : mod_seq #mod h0 h1)
  : Lemma (ensures M.modifies mod h0 h1) (decreases sq)
  = match sq with
    | MNil _ -> ()
    | MCons _ sq -> mod_of_seq mod sq
#pop-options

(* [free] *)

let rec free #a (p : t a) (sg : G.erased (list_nil a))
  : ST unit (requires fun h0 -> wf_addr_seg sg /\ freeable_seg sg /\
                             live_seg h0 sg /\
                             p == entry sg)
            (ensures fun h0 () h1 -> M.(modifies (loc_addr_seg sg) h0 h1))
  =
    if B.is_null (sgn_entry p sg) then ()
    else begin
      loc_addr_seg_includes (tail_seg sg);
      let p_next = sg_next p (G.reveal sg) in
      B.free p;
      free p_next (tail_seg sg)
    end

(* Pour une version itérative: besoin d'une boucle avec un corps ST
#push-options "--z3rlimit 30"
let free #a (p : t a) (sg0 : G.erased (list_nil a))
  : Stack unit (requires fun h0 -> wf_addr_seg sg0 /\ freeable_seg sg0 /\
                                live_seg h0 sg0 /\
                                p == entry sg0)
               (ensures fun h0 () h1 -> M.(modifies (loc_addr_seg sg0) h0 h1))
  = let h00 = ST.get () in
        loc_addr_seg_live_in h00 sg0;
    push_frame ();
    let it = B.alloca #(t a) p 1ul in
    let it_sg = B.alloca #(G.erased (list_nil a)) sg0 1ul in
    let lloc = G.hide (M.(loc_union (loc_buffer it) (loc_buffer it_sg))) in
    let h0 = ST.get () in
    let inv h : Tot prop =
      M.(modifies (loc_union lloc (loc_addr_seg sg0)) h0 h) /\
      B.live h it /\ B.live h it_sg /\
     (let p  = B.deref h it in
      let sg = B.deref h it_sg in
      p == entry sg /\
      wf_addr_seg sg /\ freeable_seg sg /\
      live_seg h sg /\
      M.loc_includes (loc_addr_seg sg0) (loc_addr_seg sg))
    in let test_inv (b:bool) h : Tot prop =
      inv h /\ (Cons? (B.deref h it_sg).segment <==> b)
    in
    let test () : Stack bool (requires fun h -> inv h) (ensures fun _ b h -> test_inv b h)
      = not (B.is_null it.(0ul))
    in let body ()
      : Stack unit (requires fun h -> inv h /\ Cons? (B.deref h it_sg).segment) (ensures fun _ () h -> inv h)
      =
          let sg = it_sg.(0ul) in
          loc_addr_seg_includes (tail_seg sg);
        let cell = it.(0ul) in
        it.(0ul) <- sg_next it.(0ul) (G.hide (G.reveal sg));
          it_sg.(0ul) <- tail_seg sg;
        B.free cell;
          let h' = ST.get () in
          assert (M.(modifies (loc_union lloc (loc_addr_seg sg0)) h0 h'))
    in
    C.Loops.while #inv #test_inv test body;
    pop_frame ()
#pop-options*)

(* [reverse] *)

let reverse_ct_hyps #a
      (sg : list_nil a) (lloc : M.loc)
      (it_f it_r : B.pointer (t a)) (sgs : B.pointer (G.erased (list_nil a & list_nil a)))
  = wf_seg sg /\
  M.(let b_it_f = loc_buffer it_f in
     let b_it_r = loc_buffer it_r in
     let b_sgs  = loc_buffer sgs  in
    loc_includes lloc (loc_union b_it_f (loc_union b_it_r b_sgs)) /\
    loc_disjoint b_it_f b_it_r /\ loc_disjoint b_it_f b_sgs /\
    loc_disjoint b_it_r b_sgs /\
    M.loc_disjoint lloc (loc_seg sg))

let reverse_ct_inv #a
      (sg : list_nil a) (lloc : M.loc)
      (it_f it_r : B.pointer (t a)) (sgs : B.pointer (G.erased (list_nil a & list_nil a)))
      (h0 h : HS.mem)
  =
    M.(modifies (loc_union lloc (loc_seg sg)) h0 h) /\
    B.(live h it_f /\ live h it_r /\ live h sgs) /\
   (let p_f = B.deref h it_f in
    let p_r = B.deref h it_r in
    let (sg_f, sg_r) = G.reveal (B.deref h sgs) in
    p_f == entry sg_f /\ p_r == entry sg_r /\
    live_seg h sg_f /\ live_seg h sg_r /\
    sg.segment == L.rev_acc sg_r.segment sg_f.segment /\
    M.(loc_includes (loc_seg sg) (loc_seg sg_f) /\
       loc_disjoint (loc_union lloc (loc_seg sg_f)) (loc_seg sg_r) /\
       wf_seg sg_f))

let reverse_ct_inv_test #a sg lloc it_f it_r
       (sgs : B.pointer (G.erased (list_nil a & list_nil a))) h0 (b:bool) h
  = reverse_ct_inv #a sg lloc it_f it_r sgs h0 h /\
    (Cons? (G.reveal (B.deref h sgs))._1.segment <==> b)

inline_for_extraction
let reverse_loop_test #a
      (sg : G.erased (list_nil a)) (lloc : G.erased M.loc)
      (it_f it_r : B.pointer (t a)) (sgs : B.pointer (G.erased (list_nil a & list_nil a)))
      h0 ()
  : Stack bool
     (requires fun h     -> reverse_ct_inv  sg lloc it_f it_r sgs h0 h)
     (ensures  fun _ b h -> reverse_ct_inv_test sg lloc it_f it_r sgs h0 b h)
  =
      let vsgs = sgs.(0ul) in
    not (B.is_null (sgn_entry it_f.(0ul) (G.reveal vsgs)._1)) 

inline_for_extraction
let reverse_loop_body #a
      (sg : G.erased (list_nil a)) (lloc : G.erased M.loc)
      (it_f it_r : B.pointer (t a)) (sgs : B.pointer (G.erased (list_nil a & list_nil a)))
      h0 ()
  : Stack unit
     (requires fun h      -> reverse_ct_hyps sg lloc it_f it_r sgs /\
                          reverse_ct_inv  sg lloc it_f it_r sgs h0 h /\
                          Cons? (G.reveal (B.deref h sgs))._1.segment)
     (ensures  fun _ () h -> reverse_ct_inv  sg lloc it_f it_r sgs h0 h)
  =
      let h = ST.get () in
      let sg_f = G.hide ((G.reveal (B.deref h sgs))._1) in
      let sg_r = G.hide ((G.reveal (B.deref h sgs))._2) in
    let cell : B.pointer (cell a) = it_f.(0ul) in
    it_f.(0ul) <- (cell.(0ul)).next;
    cell.(0ul) <- {cell.(0ul) with next = it_r.(0ul)};
    it_r.(0ul) <- cell;
      sgs.(0ul)  <- G.hide (tail_seg sg_f, {segment = L.hd sg_f.segment :: sg_r.segment; exit = B.null});
      let h' = ST.get () in G.hide (
      assert M.(modifies (loc_union lloc (loc_buffer cell)) h h');
      assert M.(modifies (loc_union lloc (loc_seg sg))     h0 h');
      let sg_f', sg_r' = G.reveal (B.deref h' sgs) in
      let hd :: tl = sg_f.segment in
      assert (sg.segment == L.rev_acc sg_r'.segment sg_f'.segment))

#push-options "--ifuel 1"
let reverse (#a : Type) (p : t a) (sg : G.erased (list_nil a))
  : Stack (t a) (requires fun h0 -> live_seg h0 sg /\
                                 wf_seg sg /\
                                 p == entry sg)
                (ensures fun h0 p' h1 -> M.modifies (loc_seg sg) h0 h1 /\
                                (let sg' = reverse_seg sg in
                                 live_seg h1 sg' /\
                                 p' == entry sg'))
  =
      let h00 = ST.get () in
    push_frame ();
      let h01 = ST.get () in
    let it_f = B.alloca #(t a) p      1ul in
    let it_r = B.alloca #(t a) B.null 1ul in
      let sgs  = B.alloca #(G.erased (list_nil a & list_nil a))
                           (G.reveal sg, empty_list a) 1ul in
      let h0 = ST.get () in
      let lloc = G.hide (M.loc_region_only true (HS.get_tip h0)) in
    assert (reverse_ct_hyps sg lloc it_f it_r sgs);
    assert (reverse_ct_inv  sg lloc it_f it_r sgs h0 h0);
    C.Loops.while #(reverse_ct_inv sg lloc it_f it_r sgs h0)
                  #(reverse_ct_inv_test sg lloc it_f it_r sgs h0)
                   (reverse_loop_test sg lloc it_f it_r sgs h0)
                   (reverse_loop_body sg lloc it_f it_r sgs h0);
    let rt = it_r.(0ul) in
      let h1 = ST.get () in
      let sg_f = G.hide ((G.reveal (B.deref h1 sgs))._1) in
      let sg_r = G.hide ((G.reveal (B.deref h1 sgs))._2) in
      assert (reverse_ct_inv  sg lloc it_f it_r sgs h0 h1);
      U.assert_by (G.reveal sg_r == reverse_seg sg) (fun () ->
        assert (G.reveal sg_f == empty_list a);
        assert (sg.segment == L.rev sg_r.segment);
        L.rev_involutive (sg_r.segment));
      assert (rt == entry sg_r);
      assert (live_seg h1 sg_r);
      assert M.(modifies (loc_union lloc (loc_seg sg)) h0 h1);
      assert M.(modifies loc_none h01 h0);
      assert M.(modifies (loc_union (loc_all_regions_from false (HS.get_tip h1)) (loc_seg sg)) h01 h1);
    pop_frame ();
      let h1' = ST.get () in
      M.modifies_fresh_frame_popped h00 h01 (loc_seg sg) h1 h1'; (* appel explicit nécessaire *)
    rt
#pop-options


(* --- length --- *)

let length_inv (a : Type0) (l : nat) (h0 : HS.mem) (r : HS.rid)
        (p     : B.pointer (t a))
        (seg   : B.pointer (Ghost.erased (list_nil a)))
        (count : B.pointer (U32.t))
        (h : HS.mem) : GTot prop
  = M.(modifies (loc_region_only true r) h0 h) /\
    B.(live h p /\ live h seg /\ live h count) /\
   (let p     = B.deref h p     in
    let seg   = B.deref h seg  in
    let count = B.deref h count in
    live_seg h seg /\ M.(loc_disjoint (loc_region_only true r) (loc_seg seg)) /\
    p == entry seg /\
    l = U32.v count + sg_length seg)

let length_test_inv a l h0 r p seg count (b : bool) h : GTot prop
  = length_inv a l h0 r p seg count h
  /\ (B.deref h p =!= B.null <==> b)

inline_for_extraction
let length_loop_test a (l : Ghost.erased nat) h0 r p seg count
  : unit -> Stack bool (requires fun h -> length_inv a l h0 r p seg count h)
                      (ensures fun _ b h -> length_test_inv a l h0 r p seg count b h)
  = fun () -> not (B.is_null (p.(0ul)))

inline_for_extraction
let length_loop_body a (l:Ghost.erased nat) h0 r
    (p     : B.pointer (t a))
    (seg   : B.pointer (Ghost.erased (list_nil a)))
    (count : B.pointer (U32.t))
  () : Stack unit
    (requires fun h     ->
            M.(loc_disjoint (loc_buffer p)   (loc_buffer seg) /\
                  loc_disjoint (loc_buffer p)   (loc_buffer count) /\
                  loc_disjoint (loc_buffer seg) (loc_buffer count) /\
                  loc_includes (loc_region_only true r)
                     (loc_union (loc_buffer p) (loc_union (loc_buffer seg) (loc_buffer count)))) /\
              l <= FStar.UInt.max_int U32.n /\
              length_test_inv a l h0 r p seg count true h)
    (ensures fun _ () h ->
              length_inv a l h0 r p seg count h)
  =
      let seg0 = seg.(0ul) in
    p.(0ul) <- (p.(0ul).(0ul)).next;
      seg.(0ul) <- Ghost.hide (tail_seg seg0);
    count.(0ul) <- U32.(count.(0ul) +^ 1ul)

let length_loop (#a : Type0) (p : t a) (sg : G.erased (list_nil a){p == entry sg}):
  Stack U32.t
    (requires fun h -> live_seg h sg /\ sg_length sg <= FStar.UInt.max_int U32.n)
    (ensures fun h0 n h1 -> M.(modifies loc_none h0 h1) /\ U32.v n = sg_length sg)
  = push_frame ();
    let p     = B.alloca #(t a) p 1ul in
    let seg   = B.alloca #(Ghost.erased (list_nil a)) sg 1ul in
    let count = B.alloca #U32.t 0ul 1ul in
    let h0 = ST.get () in
    let stack_frame = HS.get_tip h0 in
    C.Loops.while #(length_inv      a (sg_length sg) h0 stack_frame p seg count)
                  #(length_test_inv a (sg_length sg) h0 stack_frame p seg count)
                  (length_loop_test a (sg_length sg) h0 stack_frame p seg count)
                  (length_loop_body a (sg_length sg) h0 stack_frame p seg count);

    let rt = count.(0ul) in
    pop_frame ();
    rt


(* --- push --- *)

let push (#a : Type0) (r : HS.rid) (x : a) (p : t a) (sg : G.erased (list_seg a){p == entry sg}):
  ST (B.pointer (cell a))
    (requires fun h0 ->
      ST.is_eternal_region r /\
      live_seg h0 sg)
    (ensures  fun h0 rp h1 ->
      let sg' = push_seg rp x sg in
      M.(modifies loc_none h0 h1 /\
         fresh_loc (loc_buffer rp) h0 h1 /\
         loc_includes (loc_region_only true r) (loc_buffer rp)) /\
      live_seg h1 sg' /\
      rp == entry sg')
  = B.malloc r ({ data = x; next = p }) 1ul

(* --- initi --- *)

let rec initi (#a : Type0) (r : HS.rid) (lb ub : U32.t)
  (fg : G.erased ((i:nat{U32.v lb <= i /\ i < U32.v ub}) -> Tot a))
  (f : (i:U32.t) -> Pure a (requires U32.v lb <= U32.v i  /\  U32.v i < U32.v ub)
                          (ensures fun x -> x == (G.reveal fg) (U32.v i)))
  : ST (p:t a & sg:G.erased (list_nil a){p == entry sg})
       (requires fun _ -> ST.is_eternal_region r)
       (ensures  fun h0 (|_, sg|) h1 ->
         M.(modifies loc_none h0 h1 /\
            fresh_loc (loc_seg sg) h0 h1 /\
            loc_includes (loc_region_only true r) (loc_seg sg)) /\
         live_seg h1 sg /\ wf_seg sg /\
         sg_v sg == Ll.initi (U32.v lb) (U32.v ub) fg)
  = if U32.(lb <^ ub) then begin
       let fg' : G.erased ((i:nat{U32.v lb + 1 <= i /\ i < U32.v ub}) -> Tot a) =
         let fg' = G.reveal fg in G.hide fg' in
       let (|p', sg'|) = initi r U32.(lb +^ 1ul) ub fg' f in
       let p = B.malloc r ({ data = f lb; next = p' }) 1ul in
         let h' = ST.get() in
         assert (live_seg h' (push_seg p (f lb) sg'));
       (| p, G.hide (push_seg p (f lb) sg')|)
    end else
       (| B.null, G.hide (empty_list a) |)

(* --- index --- *)

let rec index (#a : Type0) (p : t a) (sg : G.erased (list_seg a){p == entry sg})
                           (i : U32.t {U32.v i < sg_length sg})
  : Stack a (requires fun h -> live_seg h sg)
            (ensures  fun h0 x h1 -> h0 == h1 /\ x == L.index (sg_v sg) (U32.v i))
  = if i = U32.zero then (p.(0ul)).data
    else
      let nx = (p.(0ul)).next in (* TODO: move p == entry sg in requires *)
      index nx (G.hide (tail_seg (G.reveal sg))) U32.(i -^ 1ul)

#push-options "--z3rlimit 10"
let index_loop (#a : Type0) (p : t a) (sg : G.erased (list_seg a){p == entry sg})
                           (i : U32.t {U32.v i < sg_length sg})
  : Stack a (requires fun h -> live_seg h sg)
            (ensures  fun h0 x h1 -> M.(modifies loc_none h0 h1) /\ x == L.index (sg_v sg) (U32.v i))
  =
  push_frame ();
  let p'  = B.alloca #(t a) p 1ul in
  let sg' = B.alloca #(G.erased (list_seg a)) sg 1ul in
  let h0 = ST.get () in
  let stack_frame = HS.get_tip h0 in
  let inv = fun h (j : nat) ->
    M.(modifies (loc_region_only true stack_frame) h0 h /\
       live h p' /\ live h sg') /\
   (let vp'  = B.deref h p'  in
    let vsg' = B.deref h sg' in
    M.(loc_disjoint (loc_region_only true stack_frame) (loc_seg vsg')) /\
    live_seg h vsg' /\ vp' == entry vsg' /\
   (let i' = U32.v i - j in
    0 <= i' /\ i' < sg_length vsg' /\
    L.index (sg_v sg) (U32.v i) == L.index (sg_v vsg') i'))
  in
  C.Loops.for 0ul i inv (fun j ->
    p'.(0ul) <- (p'.(0ul).(0ul)).next;
    let vsg' = sg'.(0ul) in
    sg'.(0ul) <- G.hide (tail_seg vsg');
    assert_norm (L.index (sg_v vsg') U32.(v i - v j) == L.index (sg_v (tail_seg vsg')) U32.((v i - v j) - 1));
    let h = ST.get () in
    assert (inv h (U32.v j + 1))
  );
  let rt = (p'.(0ul).(0ul)).data in
  pop_frame ();
  rt
#pop-options

(* --- insert --- *)

(* version fonctionnelle *)

let insert_pre (#a : Type) (r : HS.rid) (i : nat) (h0 : HS.mem) (p : t a) (sg : list_seg a)
  : Tot prop
  = ST.is_eternal_region r /\
    live_seg h0 sg /\ wf_seg sg /\
    p == entry sg /\
    i <= sg_length sg

let insert_post (#a : Type) (r : HS.rid) (i : nat) (x : a) (sg : list_seg a)
                (h0 : HS.mem) (mod : M.loc) (p1 : t a) (p_f : B.pointer (cell a)) (h1 : HS.mem)
  : Pure prop (requires i <= sg_length sg) (ensures fun _ -> True)
  = M.(modifies mod h0 h1 /\
       fresh_loc (loc_buffer p_f) h0 h1 /\
       loc_includes (loc_region_only true r) (loc_buffer p_f)) /\
    B.freeable p_f /\
   (let sg' = insert_seg i (p_f, x) sg in
    live_seg h1 sg' /\ wf_seg sg' /\
    p1 == entry sg')

#push-options "--fuel 2"

let rec insert_aux (#a : Type) (r : HS.rid) (i : U32.t) (x : a)
                   (p : t a) (sg : Ghost.erased (list_seg a))
  : ST unit (requires fun h0 -> insert_pre r (U32.v i) h0 p sg /\ U32.v i > 0)
             (ensures fun h0 () h1 -> exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h1)
  = let h0 = ST.get () in
    let hd = G.hide ((L.hd sg.segment)._1) in

    if i = 1ul then
       let p_f = B.malloc r ({next = (p.(0ul)).next; data = x}) 1ul in
       p.(0ul) <- { p.(0ul) with next = p_f };
       let h1 = ST.get () in
       introduce exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h1
            with p_f and ()
    else begin
      let next_p = G.hide ((B.deref h0 p).next) in
      insert_aux r U32.(i -^ 1ul) x ((p.(0ul)).next) (G.hide (tail_seg sg));
      let h1 = ST.get () in
      eliminate exists p_f . (insert_post r (U32.v i - 1) x (tail_seg sg) h0 (loc_seg (tail_seg sg)) next_p p_f h1)
        returns exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h1
        with prf. introduce exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h1
        with p_f and ()
    end

#pop-options

let insert (#a : Type) (r : HS.rid) (i : U32.t) (x : a) (p : t a) (sg : G.erased (list_seg a))
  : ST (t a) (requires fun h0 -> insert_pre r (U32.v i) h0 p sg)
             (ensures  fun h0 p1 h1 -> exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p1 p_f h1)
  =
  let h0 = ST.get () in
  if i = 0ul then
    let rt = B.malloc r ({next = p; data = x}) 1ul in
    let h1 = ST.get () in
    assert (insert_post r (U32.v i) x sg h0 (loc_seg sg) rt rt h1);
    rt
  else (insert_aux r i x p sg; p)


(* version itérative *)

let insert_loop_pre (#a : Type) (r : HS.rid) (x : a)
                    (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a)))
                    (i : nat) (h0 : HS.mem) : Tot prop
  = M.(live h0 l_p /\ live h0 l_sg /\ loc_disjoint (loc_buffer l_p) (loc_buffer l_sg)) /\
  ( let p = B.deref h0 l_p in let sg = B.deref h0 l_sg in
    M.(loc_disjoint (loc_union (loc_buffer l_p) (loc_buffer l_sg)) (loc_seg sg)) /\
    insert_pre r i h0 p sg)

let insert_loop_post (#a : Type) (r : HS.rid) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a)))
                     (i : nat) (h0 : HS.mem) () (h1 : HS.mem)
  : Pure prop (requires insert_loop_pre r x l_p l_sg i h0) (ensures fun _ -> True)
  = let p = B.deref h0 l_p in let sg = B.deref h0 l_sg in
     exists p_f. insert_post r i x sg h0
                 M.(loc_union (loc_union (loc_buffer l_p) (loc_buffer l_sg)) (loc_seg sg))
                 p p_f h1

let insert_post_lemma (#a : Type) (r : HS.rid) (i : nat) (x : a) (sg : list_seg a) (h0 : HS.mem)
                     (mod : M.loc) (p_f : B.pointer (cell a)) (h1 : HS.mem)
  : Lemma (requires M.loc_disjoint mod (loc_seg sg) /\
                    insert_pre #a r i h0 (entry sg) sg /\
                    1 < i /\
                    insert_post #a r (i - 1) x (tail_seg sg) h0 M.(loc_union mod (loc_seg (tail_seg sg)))
                                (entry (tail_seg sg)) p_f h1)
          (ensures  insert_post #a r i x sg h0 M.(loc_union mod (loc_seg sg)) (entry sg) p_f h1)
  = ()

inline_for_extraction
let insert_loop_body (#a : Type) (r : HS.rid) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a)))
                     (i : U32.t{U32.v i > 1})
  : Stack unit (requires fun h        -> insert_loop_pre r x l_p l_sg (U32.v i) h)
               (ensures  fun h0 () h1 -> insert_loop_pre r x l_p l_sg (U32.v i - 1) h1 /\
                                      LLoops.tail_rec_post h1
                                        (insert_loop_post r x l_p l_sg (U32.v i - 1) h1)
                                        (insert_loop_post r x l_p l_sg (U32.v i)     h0))
  =
      let h0 = ST.get () in
      let p  = G.hide (B.deref h0 l_p) in
      let sg = B.deref h0 l_sg in
      let l_locals = G.hide (M.(loc_union (loc_buffer l_p) (loc_buffer l_sg))) in
    l_p.(0ul)  <- (l_p.(0ul).(0ul)).next;
    l_sg.(0ul) <- G.hide (tail_seg (B.deref h0 l_sg));
      let h1 = ST.get () in
      let p' = G.hide (B.deref h1 l_p) in
    assert (insert_loop_pre r x l_p l_sg (U32.v i - 1) h1);
    LLoops.tail_rec_postI h1 (insert_loop_post r x l_p l_sg (U32.v i - 1) h1)
                             (insert_loop_post r x l_p l_sg (U32.v i)     h0)
      (fun () h2 ->
        eliminate exists p_f. insert_post r (U32.v i - 1) x (tail_seg sg) h1
                                     M.(loc_union l_locals (loc_seg (tail_seg sg))) p' p_f h2
          returns exists p_f. insert_post r (U32.v i) x sg h0
                                     M.(loc_union l_locals (loc_seg sg)) p p_f h2
             with prf. introduce exists p_f. insert_post r (U32.v i) x sg h0
                                                    M.(loc_union l_locals (loc_seg sg)) p p_f h2
             with p_f and insert_post_lemma r (U32.v i) x sg h1 l_locals p_f h2)

#push-options "--fuel 2"
inline_for_extraction
let insert_loop_exit (#a : Type) (r : HS.rid) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a))) ()
  : ST unit (requires fun h        -> insert_loop_pre r x l_p l_sg 1 h)
            (ensures  fun h0 () h1 -> insert_loop_post r x l_p l_sg 1 h0 () h1)
  =
      let h0 = ST.get () in
      let p  = G.hide (B.deref h0 l_p) in
      let sg = B.deref h0 l_sg in
    let p_f = B.malloc r ({next = (l_p.(0ul).(0ul)).next; data = x}) 1ul in
    (l_p.(0ul)).(0ul) <-  {l_p.(0ul).(0ul) with next = p_f };
      let h1 = ST.get () in
      introduce exists p_f. insert_post r 1 x sg h0
                                   M.(loc_union (loc_union (loc_buffer l_p) (loc_buffer l_sg)) (loc_seg sg))
                                   p p_f h1
                with p_f and ()
#pop-options

inline_for_extraction
let insert_loop_loop (#a : Type) (r : HS.rid) (i : U32.t) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a)))
  : ST unit (requires fun h -> U32.v i > 0 /\ insert_loop_pre r x l_p l_sg (U32.v i) h)
            (ensures fun h0 () h1 -> (insert_loop_post r x l_p l_sg (U32.v i) h0 () h1))
  =
      let h0 = ST.get () in
    LLoops.rec_reverse_for i 1ul
           (insert_loop_pre  r x l_p l_sg)
           (insert_loop_post r x l_p l_sg)
           (insert_loop_body r x l_p l_sg)
           (insert_loop_exit r x l_p l_sg);
      let h1 = ST.get () in
      assert (insert_loop_post r x l_p l_sg (U32.v i) h0 () h1)

let insert_loop_lemma0 #a r (x : a) p sg (l_p : B.pointer _) (l_sg : B.pointer _) i h0 h1:
  Lemma (requires i <= sg_length sg /\
                  B.deref h0 l_p == p /\ G.reveal (B.deref h0 l_sg) == sg /\
                  insert_loop_pre r x l_p l_sg i h0 /\
                  (insert_loop_post r x l_p l_sg i h0 () h1))
        (ensures exists (p_f : B.pointer (cell a)).
                    insert_post r i x sg h0
                          M.(loc_union (loc_union (loc_buffer l_p) (loc_buffer l_sg)) (loc_seg sg)) p p_f h1)
  = ()

let insert_loop_lemma1 #a r i (x : a) p sg (p_f : B.pointer (cell a)) (l_locals : M.loc) h0 h1 h2 h3 h4:
  Lemma (requires insert_pre r i h0 p sg /\
                  insert_post r i x sg h2 (M.loc_union l_locals (loc_seg sg)) p p_f h3 /\
                  M.(loc_includes (loc_all_regions_from false (HS.get_tip h1)) l_locals) /\
                  HS.fresh_frame h0 h1 /\
                  M.(modifies loc_none h1 h2) /\
                  HS.get_tip h3 == HS.get_tip h1 /\
                  HS.popped h3 h4)
        (ensures  insert_post r i x sg h0 (loc_seg sg) p p_f h4)
  =
    let sg' = { sg with segment = Ll.insert i (p_f, x) sg.segment} in

    assert M.(modifies (loc_union l_locals (loc_seg sg)) h2 h3);
    M.modifies_fresh_frame_popped h0 h1 (loc_seg sg) h3 h4;
    assert M.(modifies (loc_seg sg) h0 h4);
 
    assert (live_seg h3 sg');
    assert (live_seg h4 sg');

    assert M.(fresh_loc (loc_buffer p_f) h0 h4)

#push-options "--z3rlimit 10"
let insert_loop (#a : Type) (r : HS.rid) (i : U32.t) (x : a) (p : t a) (sg : G.erased (list_seg a))
  : ST (t a) (requires fun h0 -> insert_pre r (U32.v i) h0 p sg)
             (ensures  fun h0 p1 h1 -> exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p1 p_f h1)
  =
  let h0 = ST.get () in
  if i = 0ul then
    let rt = B.malloc r ({next = p; data = x}) 1ul in
    let h1 = ST.get () in
    introduce exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) rt p_f h1
         with rt and ();
    rt
  else begin
    push_frame ();
    let h00  = ST.get () in
    let l_p  = B.alloca #(t a) p 1ul in
    let l_sg = B.alloca #(G.erased (list_seg a)) sg 1ul in
    let l_locals = G.hide (M.(loc_union (loc_buffer l_p) (loc_buffer l_sg))) in
    let h1 = ST.get () in
    let stack_frame = G.hide (HS.get_tip h1) in
    insert_loop_loop r i x l_p l_sg;
    let h2 = ST.get () in  
    pop_frame ();
    let h3 = ST.get () in
    insert_loop_lemma0 r x p sg l_p l_sg (U32.v i) h1 h2;
    eliminate exists p_f. insert_post r (U32.v i) x sg h1 M.(loc_union l_locals (loc_seg sg)) p p_f h2
      returns exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h3
         with prf.
      introduce exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h3
           with p_f and insert_loop_lemma1 r (U32.v i) x p sg p_f l_locals h0 h00 h1 h2 h3;
    p
  end
#pop-options

(* [forward] *)

let forward_inv (#a : Type) (sg : list_seg a) (h0 : HS.mem)
                            (i : nat)  (p : t a) (h1 : HS.mem)
  : Tot prop
  = M.(modifies loc_none h0 h1) /\ p == entry (splitAt_seg i sg)._2

inline_for_extraction
let forward (#a : Type) (i : U32.t) (p : t a) (sg : G.erased (list_seg a))
  : Stack (t a) (requires fun h0    -> U32.v i <= sg_length sg /\
                                    live_seg h0 sg /\
                                    p == entry sg)
             (ensures  fun h0 p' h1 -> M.(modifies loc_none h0 h1) /\
                                    p' == entry (splitAt_seg_bd (U32.v i) sg)._2)
  = push_frame ();
    let l_p = B.alloca #(t a) p 1ul in
    let h0 = ST.get () in
    C.Loops.for 0ul i (fun h1 j -> M.(modifies (loc_buffer l_p) h0 h1) /\
                                B.live h1 l_p /\
                                B.deref h1 l_p == entry (splitAt_seg j sg)._2)
                      (fun j -> let h1 = ST.get () in
                             splitAt_next_live (U32.v j) sg h1;
                             l_p.(0ul) <- (l_p.(0ul).(0ul)).next);
    let rt = l_p.(0ul) in
    pop_frame ();
    rt

(* [set] *)

let set (#a : Type) (i : U32.t) (x : a) (p : t a) (sg : G.erased (list_seg a))
  : Stack unit (requires fun h0      -> U32.v i < sg_length sg /\
                                     live_seg h0 sg /\ wf_seg sg /\
                                     p == entry sg)
               (ensures fun h0 () h1 -> M.(modifies (loc_buffer (sg_cell sg (U32.v i))) h0 h1) /\
                                      live_seg h1 (set_seg (U32.v i) x sg))
  =
    let p' = forward i p sg in
      let h0 = ST.get () in
      let vi = U32.v i   in
      let sg0 = G.hide (splitAt_seg vi sg)._1 in
      let sg1 = G.hide (splitAt_seg vi sg)._2 in
      splitAt_seg_wf vi sg;
      splitAt_seg_live vi h0 sg;
      L.splitAt_length vi sg.segment;
      L.lemma_splitAt_reindex_right vi sg.segment 0;
      assert (live_seg h0 sg1);
    p'.(0ul) <- { p'.(0ul) with data = x };
      let h1 = ST.get () in
      U.assert_by (live_seg h1 (append_seg sg0 (set_seg 0 x sg1))) (fun () ->
          assert (live_seg h1 (set_seg 0 x sg1));
          assert (live_seg h1 sg0));
      set_seg_splitAt (U32.v i) 0 x sg

(* [last] *)

let last_ct_locals #a (l_it : B.pointer (B.pointer (cell a))) (l_k  : B.pointer (G.erased nat))
  : GTot M.loc =
  M.(loc_union (loc_buffer l_it) (loc_buffer l_k))

let last_ct_hyps #a (sg : list_nil a) c_h0 l_it l_k : prop =
  M.(loc_disjoint (last_ct_locals l_it l_k) (loc_seg sg) /\
     loc_disjoint (loc_buffer l_it) (loc_buffer l_k)) /\
  live_seg c_h0 sg

let last_loop_inv #a sg c_h0 (l_it : B.pointer (B.pointer (cell a))) (l_k  : B.pointer (G.erased nat))
                  (h : HS.mem) : prop =
  M.(modifies (loc_union (loc_buffer l_it) (loc_buffer l_k)) c_h0 h /\
     live h l_it /\ live h l_k) /\
 (let vit = B.deref h l_it in
  let vk  = B.deref h l_k  in
  vk < sg_length #a sg /\
  vit == entry (splitAt_seg_bd vk sg)._2)


let lemma_last_loop_inv_it_live #a (sg : list_nil a) c_h0
             (l_it : B.pointer (B.pointer (cell a))) (l_k  : B.pointer (G.erased nat)) h
  : Lemma (requires last_ct_hyps sg c_h0 l_it l_k /\ last_loop_inv sg c_h0 l_it l_k h)
          (ensures (let sg1 = (splitAt_seg_bd (B.deref h l_k) sg)._2 in
                    live_seg h sg1 /\ Cons? sg1.segment))
  = let vk = B.deref h l_k in
    assert (live_seg h sg);
    splitAt_seg_live vk h sg

#push-options "--fuel 2"

inline_for_extraction
let last_loop_body #a (sg : G.erased (list_nil a)) c_h0
             (l_it : B.pointer (B.pointer (cell a))) (l_k  : B.pointer (G.erased nat)) ()
  : Stack unit (requires fun h      -> last_ct_hyps sg c_h0 l_it l_k /\
                                    last_loop_inv sg c_h0 l_it l_k h /\
                                    ~B.(g_is_null (deref h (deref h l_it)).next))
               (ensures  fun _ () h -> last_loop_inv sg c_h0 l_it l_k  h)
  =
      let h0  = ST.get () in
      let k0  = B.deref h0 l_k in
      let sg0 = G.hide ((splitAt_seg_bd k0 sg)._2) in
      lemma_last_loop_inv_it_live sg c_h0 l_it l_k h0;
    l_it.(0ul) <- sg_next (l_it.(0ul)) sg0; 
    l_k.(0ul)  <- k0 + 1;
      let h1  = ST.get () in
      U.assert_by (tail_seg sg0 == (splitAt_seg (k0 + 1) sg)._2)
                  (fun () -> splitAt_next k0 sg)

let last (#a : Type) (p : t a) (sg : G.erased (list_nil a))
  : Stack (t a) (requires fun h0      -> live_seg h0 sg /\
                                      p == entry sg /\
                                      sg_length sg > 0)
                (ensures fun h0 p' h1 -> M.(modifies loc_none h0 h1) /\
                                     (let sg' = (splitAt_seg_bd (sg_length sg - 1) sg)._2 in
                                      p' == entry sg'))
  =
    push_frame ();
    let it = B.alloca #(B.pointer (cell a)) p 1ul in
    let k  = B.alloca #(G.erased nat) 0 1ul         in
      let h0 = ST.get () in
      assert (last_ct_hyps sg h0 it k);
      let inv = last_loop_inv sg h0 it k in
      let test_post (b : bool) (h : HS.mem) =
        inv h /\ (B.(g_is_null (deref h (deref h it)).next) <==> not b)
    in
    let test () : Stack bool (requires fun h -> inv h) (ensures fun _ b h -> test_post b h)
      = let h = ST.get () in lemma_last_loop_inv_it_live sg h0 it k h;
        not (B.is_null (it.(0ul).(0ul)).next)
    in
    C.Loops.while #(fun h -> inv h) #test_post test (last_loop_body sg h0 it k);
      let h1 = ST.get () in
      lemma_last_loop_inv_it_live sg h0 it k h1;
      assert (sg_length (splitAt_seg_bd (B.deref h1 k) sg)._2 == 1);
      assert (G.reveal (B.deref h1 k) = sg_length sg - 1);
    let rt = it.(0ul) in
    pop_frame ();
    rt

#pop-options

(* [append] *)

#push-options "--fuel 2"
let append (#a : Type) (p0 : t a) (sg0 : G.erased (list_nil a)) (p1 : t a) (sg1 : G.erased (list_seg a))
  : Stack (t a) (requires fun h0 -> live_seg h0 sg0 /\
                                 wf_seg sg0 /\ M.loc_disjoint (loc_seg sg0) (loc_seg sg1) /\
                                 p0 == entry sg0 /\
                                 p1 == entry sg1)
                (ensures fun h0 p h1 -> M.modifies (loc_seg sg0) h0 h1 /\
                                   ( let sg = append_seg ({sg0 with exit = entry sg1}) sg1 in
                                     p == entry sg /\
                                    (live_seg h0 sg1 ==> live_seg h1 sg)))
  =
      let h00 = ST.get () in
    if B.is_null p0 then p1
    else begin
      let p0_last = last p0 sg0 in
        let h0 = ST.get () in
        let sg00 = G.hide (splitAt_seg_bd (sg_length sg0 - 1) sg0)._1 in
        let sg01 = G.hide (splitAt_seg_bd (sg_length sg0 - 1) sg0)._2 in
        splitAt_append_seg (sg_length sg0 - 1) sg0;
        splitAt_seg_live (sg_length sg0 - 1) h0 sg0;
        splitAt_seg_wf   (sg_length sg0 - 1) sg0;
        assert (p0_last == entry sg01);
        assert (live_seg h0 sg01);
        assert M.(loc_includes (loc_seg sg0) (loc_buffer (L.hd sg01.segment)._1));
      p0_last.(0ul) <- { p0_last.(0ul) with next = p1 };
        let h1 = ST.get () in
        assert M.(modifies (loc_seg sg0) h0 h1);
        assert (live_seg h1 sg00);
        assert (live_seg h1 ({sg01 with exit = p1})); 
        assert ({sg0 with exit = entry sg1} == append_seg sg00 ({sg01 with exit = p1}));
      p0
    end
#pop-options

(* ------------------------------------------------------------------------------------------- *)

let length_loop_u32 = length_loop #U32.t

let initi_u32 = initi #U32.t

let initi_id_f (i : U32.t) : Pure U32.t (requires True) (ensures fun x -> x = i) = i

let initi_id (r : HS.rid{ST.is_eternal_region r}) (lb ub : U32.t) =
  initi #U32.t r lb ub (G.hide (fun i -> U32.uint_to_t i)) initi_id_f

let index_u32 = index #U32.t

let index_loop_u32 = index_loop #U32.t

let insert_u32 = insert #U32.t

let insert_loop_u32 = insert_loop #U32.t

let forward_u32 = forward #U32.t

let set_u32 = set #U32.t

let last_u32 = last #U32.t

let append_u32 = append #U32.t

let reverse_u32 = reverse #U32.t

let free_u32 = free #U32.t

let test_for () : Stack unit (fun _ -> True) (fun _ _ _ -> True)
  =
    C.Loops.for 0ul 10ul (fun _ _ -> True) (fun _ -> ())

(*
let test_reverse_for () : Stack unit (fun _ -> True) (fun _ _ _ -> True)
  =
    C.Loops.reverse_for 10ul 0ul (fun _ _ -> True) (fun _ -> ())
*)

let test_ghost () : Stack unit (fun _ -> True) (fun _ _ _ -> True)
  = push_frame ();
    let b = B.alloca #(G.erased nat) (G.hide 0) 1ul in
    b.(0ul) <- 42;
    pop_frame ()

#push-options "--fuel 2"
let test () : Stack unit (fun _ -> True) (fun _ _ _ -> True)
  = push_frame ();
    let b = B.alloca ({next=B.null; data=42ul}) 1ul in
    let h = ST.get () in
    let sg : list_nil U32.t = {segment = [b, 42ul]; exit = B.null} in
    assert (b == entry sg);
    assert (live_seg h sg);
    pop_frame ()
#pop-options
