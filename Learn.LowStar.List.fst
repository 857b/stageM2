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

#push-options "--__no_positivity"
noeq
type t (a: Type0) =
  B.pointer_or_null (cell a)
and cell (a: Type0) = {
  next: t a;
  data: a;
}
#pop-options

noeq
type list_seg (a : Type0) = {
  segment : list (B.pointer (cell a) & a);
  exit    : t a;
}

let list_nil (a : Type0) : Type = sg:list_seg a{sg.exit == B.null}

unfold let sg_v (#a : Type0) (sg : list_seg a) : Tot (list a)
  = L.map snd sg.segment

unfold let sg_length (#a : Type0) (sg : list_seg a) : Tot nat
  = L.length sg.segment

let entry (#a : Type0) (sg : list_seg a) : Tot (t a)
  = if Nil? sg.segment then sg.exit else (L.hd sg.segment)._1

unfold let tail_seg (#a : Type0) (sg : list_seg a)
  : Pure (list_seg a) (requires Cons? sg.segment) (ensures fun _ -> True)
  = {sg with segment = L.tail sg.segment}

unfold let append_seg (#a : Type0) (sg0 sg1 : list_seg a) : Tot (list_seg a)
  = { segment = L.(sg0.segment @ sg1.segment);
      exit    = sg1.exit }

let rec loc_seg (#a : Type) (sg : list_seg a) : GTot M.loc
  (decreases sg.segment)
  = match sg.segment with
    | [] -> M.loc_none
    | hd :: tl -> M.(loc_union (loc_buffer hd._1) (loc_seg (tail_seg sg)))

let rec wf_seg (#a : Type) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> (M.loc_disjoint (B.loc_buffer hd._1) (loc_seg (tail_seg sg)))
             /\ wf_seg (tail_seg sg)

let rec live_seg (#a : Type) (h : HS.mem) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> let sg' = tail_seg sg in 
               B.live h hd._1 /\ B.deref h hd._1 == {next = entry sg'; data = hd._2} /\ live_seg h sg'

let rec loc_seg_live_in (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg) (ensures B.loc_in (loc_seg sg) h)
          (decreases sg.segment)
    [SMTPat (live_seg h sg)]
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_seg_live_in h (tail_seg sg)

let rec loc_seg_fold (#a : Type) (sg : list_seg a)
  : Lemma (ensures loc_seg sg == L.fold_right_gtot sg.segment (fun c -> M.(loc_union (loc_buffer c._1))) M.loc_none)
          (decreases sg.segment)
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_seg_fold (tail_seg sg)

let append_seg_assoc (#a : Type) (sg0 sg1 sg2 : list_seg a)
  : Lemma (ensures append_seg sg0 (append_seg sg1 sg2) == append_seg (append_seg sg0 sg1) sg2)
  = L.append_assoc sg0.segment sg1.segment sg2.segment

let rec append_seg_loc (#a : Type) (sg0 sg1 : list_seg a)
  : Lemma (ensures loc_seg (append_seg sg0 sg1) == M.loc_union (loc_seg sg0) (loc_seg sg1))
          (decreases sg0.segment)
          [SMTPat (loc_seg (append_seg sg0 sg1))]
  = match sg0.segment with
    | [] -> ()
    | hd :: _ ->
      append_seg_loc (tail_seg sg0) sg1;
      M.loc_union_assoc (M.loc_buffer hd._1) (loc_seg (tail_seg sg0)) (loc_seg sg1)

let rec append_seg_wf (#a : Type) (sg0 sg1 : list_seg a)
  : Lemma (ensures wf_seg (append_seg sg0 sg1) <==>
                   wf_seg sg0 /\ wf_seg sg1 /\ M.loc_disjoint (loc_seg sg0) (loc_seg sg1))
          (decreases sg0.segment)
          [SMTPat (wf_seg (append_seg sg0 sg1))]
  = match sg0.segment with
    | [] -> ()
    | _ :: _ -> append_seg_wf (tail_seg sg0) sg1

let rec append_seg_live (#a : Type) (h : HS.mem) (sg0 sg1 : list_seg a)
  : Lemma (requires sg0.exit == entry sg1)
          (ensures live_seg h (append_seg sg0 sg1) <==> live_seg h sg0 /\ live_seg h sg1)
          (decreases sg0.segment)
          [SMTPat (live_seg h (append_seg sg0 sg1))]
  = match sg0.segment with
    | [] -> ()
    | _ :: _ -> append_seg_live h (tail_seg sg0) sg1

(*
let rec loc_disjoint_seg_for_all (#a : Type) (loc : M.loc) (sg : list_seg a)
  : Lemma (ensures M.loc_disjoint loc (loc_seg sg)
                   <==> Ll.for_allP (M.loc_disjoint loc)
                                  (L.map_gtot (fun (c : B.pointer (cell a) & a) -> M.loc_buffer c._1) sg.segment))
  = admit ()
*)

let rec frame (#a : Type) (h0 h1 : HS.mem) (sg : list_seg a) (r : B.loc)
  : Lemma (requires live_seg h0 sg /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_seg sg)))
          (ensures  live_seg h1 sg)
          (decreases sg.segment)
    [SMTPat (live_seg h0 sg); SMTPat (M.modifies r h0 h1)]
  = match sg.segment with
    | [] -> ()
    | hd :: tl -> frame h0 h1 (tail_seg sg) r


noextract let empty_list (a : Type0) : list_nil a = { segment = []; exit = B.null }
let empty_live (a : Type0) (h : HS.mem) : Lemma (live_seg h (empty_list a)) = ()

let null_is_empty (#a : Type0) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ entry sg == B.null)
          (ensures  sg == empty_list a)
  = match sg.segment with
    | [] -> ()


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
  (() : squash M.(loc_disjoint (loc_buffer p)   (loc_buffer seg) /\
                  loc_disjoint (loc_buffer p)   (loc_buffer count) /\
                  loc_disjoint (loc_buffer seg) (loc_buffer count) /\
                  loc_includes (loc_region_only true r)
                     (loc_union (loc_buffer p) (loc_union (loc_buffer seg) (loc_buffer count)))))
  (() : squash (l <= FStar.UInt.max_int U32.n))
  : unit -> Stack unit (requires fun h -> length_test_inv a l h0 r p seg count true h)
                      (ensures fun _ () h -> length_inv a l h0 r p seg count h)
  = fun () -> p.(0ul) <- (p.(0ul).(0ul)).next;
           let seg0 = seg.(0ul) in
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
                  (length_loop_body a (sg_length sg) h0 stack_frame p seg count () ());

    let rt = count.(0ul) in
    pop_frame ();
    rt


(* --- push --- *)

let push_seg (#a : Type0) (p : B.pointer (cell a)) (x : a) (sg : list_seg a) : list_seg a
  = { sg with segment = (p,x) :: sg.segment }

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
         let fg' = G.reveal fg in G.hide fg'  in
       let (|p', sg'|) = initi r U32.(lb +^ 1ul) ub fg' f in
       let p = B.malloc r ({ data = f lb; next = p' }) 1ul in
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

let loc_union_comm12 (s0 s1 s2 : M.loc)
  : Lemma M.(loc_union s0 (loc_union s1 s2) == loc_union s1 (loc_union s0 s2))
  = M.(loc_union_assoc s0 s1 s2; loc_union_comm s0 s1; loc_union_assoc s1 s0 s2)

let rec insert_seg_loc (#a : Type) (i : nat) (x : B.pointer (cell a) & a) (sg : list_seg a)
  : Lemma (requires i <= sg_length sg)
          (ensures loc_seg ({sg with segment = Ll.insert i x sg.segment})
                   == M.(loc_union (loc_buffer x._1) (loc_seg sg)))
          (decreases i)
          [SMTPat (loc_seg ({sg with segment = Ll.insert i x sg.segment}))]
  = if i = 0 then ()
    else let hd = (L.hd sg.segment)._1 in (
         insert_seg_loc (i - 1) x (tail_seg sg);
         M.(loc_union_comm12 (loc_buffer hd) (loc_buffer x._1) (loc_seg (tail_seg sg)))
    )

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
   (let sg' = {sg with segment = Ll.insert i (p_f, x) sg.segment} in
    live_seg h1 sg' /\ wf_seg sg' /\
    p1 == entry sg')

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
  = M.(live h0 l_p /\live h0 l_sg /\ loc_disjoint (loc_buffer l_p) (loc_buffer l_sg)) /\
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

inline_for_extraction
let insert_loop_exit (#a : Type) (r : HS.rid) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a))) (_:unit)
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

inline_for_extraction
let insert_loop_loop (#a : Type) (r : HS.rid) (i : U32.t) (x : a)
                     (l_p : B.pointer (t a)) (l_sg : B.pointer (G.erased (list_seg a)))
  : ST unit (requires fun h -> U32.v i > 0 /\ insert_loop_pre r x l_p l_sg (U32.v i) h)
            (ensures fun h0 () h1 -> U.hide_prop (insert_loop_post r x l_p l_sg (U32.v i) h0 () h1))
  =
      let h0 = ST.get () in
    LLoops.rec_reverse_for i 1ul
           (insert_loop_pre  r x l_p l_sg)
           (insert_loop_post r x l_p l_sg)
           (insert_loop_body r x l_p l_sg)
           (insert_loop_exit r x l_p l_sg);
      let h1 = ST.get () in
      U.hide_propI (insert_loop_post r x l_p l_sg (U32.v i) h0 () h1)

let insert_loop_lemma0 #a r (x : a) p sg (l_p : B.pointer _) (l_sg : B.pointer _) i h0 h1:
  Lemma (requires i <= sg_length sg /\
                  B.deref h0 l_p == p /\ G.reveal (B.deref h0 l_sg) == sg /\
                  insert_loop_pre r x l_p l_sg i h0 /\
                  U.hide_prop (insert_loop_post r x l_p l_sg i h0 () h1))
        (ensures exists (p_f : B.pointer (cell a)).
                    insert_post r i x sg h0
                          M.(loc_union (loc_union (loc_buffer l_p) (loc_buffer l_sg)) (loc_seg sg)) p p_f h1)
  = U.hide_propD (insert_loop_post r x l_p l_sg i h0 () h1)

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

    assert M.(fresh_loc (loc_buffer p_f) h2 h3);
    assert M.(fresh_loc (loc_buffer p_f) h0 h4);

    assert (live_seg h3 sg');
    assert (live_seg h4 sg')

inline_for_extraction
let insert_loop0 (#a : Type) (r : HS.rid) (i : U32.t) (x : a) (p : t a) (sg : G.erased (list_seg a))
  : ST (t a) (requires fun h0 -> insert_pre r (U32.v i) h0 p sg)
             (ensures  fun h0 p1 h1 -> U.hide_prop (exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p1 p_f h1))
  =
  let h0 = ST.get () in
  if i = 0ul then
    let rt = B.malloc r ({next = p; data = x}) 1ul in
    let h1 = ST.get () in
    U.hide_propI_by
      (exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) rt p_f h1)
      (fun () -> assert (insert_post r (U32.v i) x sg h0 (loc_seg sg) rt rt h1));
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
    U.hide_propI_by (exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h3) (fun () ->
      insert_loop_lemma0 r x p sg l_p l_sg (U32.v i) h1 h2;
      eliminate exists p_f. insert_post r (U32.v i) x sg h1 M.(loc_union l_locals (loc_seg sg)) p p_f h2
        returns exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h3
           with prf.
      introduce exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p p_f h3
           with p_f and insert_loop_lemma1 r (U32.v i) x p sg p_f l_locals h0 h00 h1 h2 h3
    );
    p
  end

let insert_loop (#a : Type) (r : HS.rid) (i : U32.t) (x : a) (p : t a) (sg : G.erased (list_seg a))
  : ST (t a) (requires fun h0 -> insert_pre r (U32.v i) h0 p sg)
             (ensures  fun h0 p1 h1 -> exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) p1 p_f h1)
  = let h0 = ST.get () in
    let rt = insert_loop0 r i x p sg in
    let h1 = ST.get () in
    U.hide_propD (exists p_f. insert_post r (U32.v i) x sg h0 (loc_seg sg) rt p_f h1);
    rt


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

let test () : Stack unit (fun _ -> True) (fun _ _ _ -> True)
  = push_frame ();
    let b = B.alloca ({next=B.null; data=42ul}) 1ul in
    let h = ST.get () in
    let sg : list_nil U32.t = {segment = [b, 42ul]; exit = B.null} in
    assert (b == entry sg);
    assert (live_seg h sg);
    pop_frame ()
