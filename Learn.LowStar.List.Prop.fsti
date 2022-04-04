module Learn.LowStar.List.Prop

module UL  = Learn.LowStar.Util
module L   = FStar.List.Pure
module Ll  = Learn.List
module B   = LowStar.Buffer
module M   = LowStar.Modifies
module G   = FStar.Ghost
module HS  = FStar.HyperStack
module ST  = FStar.HyperStack.ST

open LowStar.BufferOps
open FStar.HyperStack.ST

open Learn.LowStar.List.Data

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

let sg_cell (#a : Type0) (sg : list_seg a) (i : nat)
  : Ghost (B.pointer (cell a)) (requires i < sg_length sg) (ensures fun _ -> True)
  = (L.index sg.segment i)._1

let entry (#a : Type0) (sg : list_seg a) : Tot (t a)
  = if Nil? sg.segment then sg.exit else (L.hd sg.segment)._1

let cons_seg (#a : Type0) (hd : B.pointer (cell a) & a) (sg : list_seg a) : list_seg a
  = { sg with segment = hd :: sg.segment }

let tail_seg (#a : Type0) (sg : list_seg a)
  : Pure (list_seg a) (requires Cons? sg.segment) (ensures fun _ -> True)
  = {sg with segment = L.tail sg.segment}

(** Pédicats *)

let rec loc_seg (#a : Type) (sg : list_seg a) : GTot M.loc
  (decreases sg.segment)
  = match sg.segment with
    | [] -> M.loc_none
    | hd :: tl -> M.(loc_union (loc_buffer hd._1) (loc_seg (tail_seg sg)))

(* Utiliser uniquement cette version ? *)
let rec loc_addr_seg (#a : Type) (sg : list_seg a) : GTot M.loc
  (decreases sg.segment)
  = match sg.segment with
    | [] -> M.loc_none
    | hd :: tl -> M.(loc_union (loc_addr_of_buffer hd._1) (loc_addr_seg (tail_seg sg)))

let rec wf_seg (#a : Type) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> (M.loc_disjoint (B.loc_buffer hd._1) (loc_seg (tail_seg sg)))
             /\ wf_seg (tail_seg sg)

let rec wf_addr_seg (#a : Type) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> (M.loc_disjoint (B.loc_addr_of_buffer hd._1) (loc_addr_seg (tail_seg sg)))
             /\ wf_addr_seg (tail_seg sg)

let freeable_seg (#a : Type) (sg : list_seg a) : Tot prop
  = Ll.g_for_allP sg.segment (fun x -> B.freeable x._1)

let rec live_seg_def (#a : Type) (h : HS.mem) (sg : list_seg a) : Tot prop
  (decreases sg.segment)
  = match sg.segment with
    | [] -> True
    | hd :: tl -> let sg' = tail_seg sg in 
               B.live h hd._1 /\ B.deref h hd._1 == {next = entry sg'; data = hd._2} /\ live_seg_def h sg'

val live_seg (#a : Type) (h : HS.mem) (sg : list_seg a) : Tot prop

val live_seg_unfold : a:Type -> Lemma (live_seg #a == live_seg_def #a)

(** Lemmes sur les prédicats *)

val loc_seg_live_in (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg) (ensures B.loc_in (loc_seg sg) h)
          (decreases sg.segment)
    [SMTPat (live_seg h sg)]

val loc_addr_seg_live_in (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg) (ensures B.loc_in (loc_addr_seg sg) h)
          (decreases sg.segment)

let rec loc_addr_seg_includes (#a : Type) (sg : list_seg a)
  : Lemma (ensures M.loc_includes (loc_addr_seg sg) (loc_seg sg))
          (decreases sg.segment)
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_addr_seg_includes (tail_seg sg)


let rec loc_seg_includes_cell (#a : Type) (sg : list_seg a) (i : nat)
  : Lemma (requires  i < sg_length sg)
          (ensures   M.(loc_includes (loc_seg sg) (loc_buffer (sg_cell sg i))))
          (decreases i)
          [SMTPat (sg_cell sg i); SMTPat (loc_seg sg)]
  = if i = 0 then () else loc_seg_includes_cell (tail_seg sg) (i - 1)

let loc_seg_fold_f #a (c : B.pointer (cell a) & a) : M.loc -> GTot M.loc
  = M.(loc_union (loc_buffer c._1))

let loc_seg_fold_f_comm a :
  Lemma (ensures Ll.fold_right_gtot_f_comm (loc_seg_fold_f #a))
  = let f = loc_seg_fold_f #a in
    introduce forall x0 x1 y . f x0 (f x1 y) == f x1 (f x0 y)
      with UL.loc_union_comm12 M.(loc_buffer x0._1) M.(loc_buffer x1._1) y

let rec loc_seg_fold (#a : Type) (sg : list_seg a)
  : Lemma (ensures loc_seg sg == L.fold_right_gtot sg.segment loc_seg_fold_f M.loc_none)
          (decreases sg.segment)
  = match sg.segment with
    | [] -> ()
    | _ :: _ -> loc_seg_fold (tail_seg sg)

val frame (#a : Type) (h0 h1 : HS.mem) (sg : list_seg a) (r : B.loc)
  : Lemma (requires live_seg h0 sg /\ M.(modifies r h0 h1 /\ loc_disjoint r (loc_seg sg)))
          (ensures  live_seg h1 sg)
          (decreases sg.segment)
    [SMTPat (live_seg #a h0 sg); SMTPat (M.modifies r h0 h1)]
    (* or [SMTPat (M.modifies r h0 h1); SMTPat (live_seg #a h1 sg)] ? *)


(** Manipulation des segments *)

noextract let empty_seg  (#a : Type) (exit : B.pointer_or_null (cell a)) = { segment = []; exit }
noextract let empty_list (a : Type0) : list_nil a = empty_seg B.null
val empty_live (#a : Type) (exit : B.pointer_or_null (cell a)) (h : HS.mem)
  : Lemma (live_seg h (empty_seg #a exit)) [SMTPat (live_seg h (empty_seg #a exit))]

val sg_mkcons_lem (#a : Type) (h : HS.mem) (hd : B.pointer (cell a) & a) (tl : list_seg a)
  : Lemma (requires B.live h hd._1 /\
                    B.deref h hd._1 == {next = entry tl; data=hd._2} /\
                    live_seg h tl)
          (ensures  live_seg h (cons_seg hd tl))

val sg_uncons_lem (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ Cons? sg.segment)
          (ensures  (let cell, data = L.hd sg.segment in
                     let tl = tail_seg sg in
                     B.live h cell /\
                     B.deref h cell == {next = entry tl; data} /\
                     live_seg h tl))

inline_for_extraction
let sg_uncons (#a : Type) (sg : G.erased (list_seg a))
  : Stack (G.erased (B.pointer (cell a)) & G.erased a & G.erased (list_seg a))
          (requires fun h -> live_seg h sg /\ Cons? sg.segment)
          (ensures  fun h (cell, data, tl) h' -> h' == h /\
                     sg.segment == (G.reveal cell, G.reveal data) :: tl.segment /\
                     G.reveal tl == tail_seg sg /\
                     B.live h cell /\
                     B.deref h cell == {next = entry tl; data} /\
                     live_seg h tl)
  =
    let h = ST.get () in sg_uncons_lem h sg;
    G.hide (L.hd sg.segment)._1,
    G.hide (L.hd sg.segment)._2,
    G.hide (tail_seg sg)

inline_for_extraction
let sg_mkcons (#a : Type) (hd : G.erased (B.pointer (cell a) & a)) (tl : G.erased (list_seg a))
  : Stack (G.erased (list_seg a))
          (requires fun h -> let cell, data = G.reveal hd in
                          B.live h cell /\
                          B.deref h cell == {next = entry tl; data} /\
                          live_seg h tl)
          (ensures  fun h sg h' -> h' == h /\
                          G.reveal sg == cons_seg hd tl /\
                          live_seg h sg)
  = let h = ST.get () in sg_mkcons_lem h hd tl;
    G.hide (cons_seg hd tl)
    
val entry_null_is_empty (#a : Type) (h : HS.mem) (sg : list_seg a)
  : Lemma (requires live_seg h sg /\ entry sg == B.null)
          (ensures  sg == empty_list a)
          [SMTPat (live_seg h sg)]

val list_nil_entry_nnull (#a : Type) (h : HS.mem) (sg : list_nil a)
  : Lemma (requires live_seg h sg /\ entry sg =!= B.null)
          (ensures  Cons? sg.segment)
          [SMTPat (live_seg h sg); SMTPat (Cons? sg.segment)]

inline_for_extraction
val sgn_entry (#a : Type) (p : t a) (sg : G.erased (list_nil a))
  : Stack (t a) (requires fun h0       -> live_seg h0 sg /\ p == entry sg)
                (ensures  fun h0 p' h1 -> h0 == h1 /\ B.live h1 p /\ p' == p)

inline_for_extraction
val sg_next (#a : Type) (p : t a) (sg : G.erased (list_seg a))
  : Stack (t a) (requires fun h0       -> live_seg h0 sg /\ p == entry sg /\ Cons? sg.segment)
                (ensures  fun h0 p' h1 -> h0 == h1 /\
                                       live_seg h1 (tail_seg sg) /\ p' == entry (tail_seg sg))


(** opérations *)

(* [append_seg] *)

let append_seg (#a : Type0) (sg0 sg1 : list_seg a) : Tot (list_seg a)
  = { segment = L.(sg0.segment @ sg1.segment);
      exit    = sg1.exit }

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

val append_seg_live (#a : Type) (h : HS.mem) (sg0 sg1 : list_seg a)
  : Lemma (requires sg0.exit == entry sg1)
          (ensures live_seg h (append_seg sg0 sg1) <==> live_seg h sg0 /\ live_seg h sg1)
          (decreases sg0.segment)
          [SMTPat (live_seg h (append_seg sg0 sg1))]

(* [insert_seg] *)

let insert_seg (#a : Type0) (i : nat) (x : B.pointer (cell a) & a) (sg : list_seg a)
  : Pure (list_seg a) (requires i <= sg_length sg) (ensures fun _ -> True)
  = { sg with segment = Ll.insert i x sg.segment }

let rec insert_seg_loc (#a : Type) (i : nat) (x : B.pointer (cell a) & a) (sg : list_seg a)
  : Lemma (requires i <= sg_length sg)
          (ensures loc_seg (insert_seg i x sg) == M.(loc_union (loc_buffer x._1) (loc_seg sg)))
          (decreases i)
          [SMTPat (loc_seg (insert_seg i x sg))]
  = if i = 0 then ()
    else begin let hd = (L.hd sg.segment)._1 in
         insert_seg_loc (i - 1) x (tail_seg sg);
         M.(UL.loc_union_comm12 (loc_buffer hd) (loc_buffer x._1) (loc_seg (tail_seg sg)))
    end

(* [splitAt_seg] *)

let splitAt_seg (#a:Type) (n:nat) (sg:list_seg a) : Tot (list_seg a & list_seg a) =
  let l0, l1 = L.splitAt n sg.segment in
  let sg1 = {segment = l1; exit = sg.exit} in
  {segment = l0; exit = entry sg1}, sg1

unfold let splitAt_seg_bd (#a:Type) (n:nat) (sg:list_seg a)
  : Pure (list_seg a & list_seg a)
         (requires n <= sg_length sg)
         (ensures fun (sg0,sg1) -> sg_length sg0 = n /\ sg_length sg1 = sg_length sg - n)
  = L.splitAt_length n sg.segment;
    splitAt_seg n sg

let splitAt_append_seg (#a:Type) (n:nat) (sg:list_seg a)
  : Lemma (let sg0,sg1 = splitAt_seg n sg in append_seg sg0 sg1 == sg)
  = Ll.lemma_splitAt_append n sg.segment

let splitAt_seg_wf (#a : Type) (n:nat) (sg : list_seg a)
  : Lemma (let sg0,sg1 = splitAt_seg n sg in
          (wf_seg sg <==> wf_seg sg0 /\ wf_seg sg1 /\ M.loc_disjoint (loc_seg sg0) (loc_seg sg1)))
  = splitAt_append_seg n sg

let splitAt_seg_live (#a:Type) (n:nat) (h : HS.mem) (sg:list_seg a)
  : Lemma (let sg0,sg1 = splitAt_seg n sg in
          (live_seg h sg <==> live_seg h sg0 /\ live_seg h sg1))
  = splitAt_append_seg n sg

let splitAt_seg_entry (#a:Type) (n:nat) (sg:list_seg a)
  : Lemma (entry (splitAt_seg n sg)._1 == entry sg)
  = ()

let rec splitAt_next (#a : Type) (i : nat) (sg : list_seg a)
  : Lemma (requires i < sg_length sg)
          (ensures  (splitAt_seg_bd (i + 1) sg)._2 == tail_seg (splitAt_seg_bd i sg)._2)
          (decreases i)
  = if i = 0 then () else splitAt_next (i - 1) (tail_seg sg)

let rec splitAt_next_live (#a : Type) (i : nat) (sg : list_seg a) (h : HS.mem)
  : Lemma (requires live_seg h sg /\ i < sg_length sg)
          (ensures (let sg1 = (splitAt_seg_bd i sg)._2 in
                    let ptr = entry sg1 in
                    Cons? sg1.segment /\
                    (splitAt_seg_bd (i+1) sg)._2 == tail_seg sg1 /\
                    ~(B.g_is_null ptr) /\ B.live h ptr /\
                    (B.deref h ptr).next == entry (tail_seg sg1)))
          (decreases i)
  =
    splitAt_seg_live i h sg;
    sg_uncons_lem h sg;
    if i = 0 then ()
    else begin
      splitAt_next_live (i-1) (tail_seg sg) h
    end

(* [set_seg] *)

let set_seg (#a : Type) (i : nat) (x : a) (sg : list_seg a)
  : Pure (list_seg a) (requires i < sg_length sg) (ensures fun sg' -> sg_length sg' = sg_length sg)
  = { sg with segment = Ll.map_index i (fun (c, _) -> (c, x)) sg.segment }

let rec set_seg_splitAt (#a : Type) (i j : nat) (x : a) (sg : list_seg a)
  : Lemma (requires i + j < sg_length sg)
          (ensures  set_seg (i + j) x sg
                    == (let sg0,sg1 = splitAt_seg_bd i sg in
                        append_seg sg0 (set_seg j x sg1)))
          (decreases i)
  = if i = 0 then ()
    else (set_seg_splitAt (i-1) j x (tail_seg sg);
          L.splitAt_length i sg.segment)

(* [reverse_seg] *)

let reverse_seg (#a : Type) (sg : list_seg a) =
  { segment = L.rev sg.segment; exit = B.null }

let reverse_seg_loc (#a : Type) (sg : list_seg a)
  : Lemma (ensures loc_seg (reverse_seg sg) == loc_seg sg)
    [SMTPat (loc_seg (reverse_seg sg))]
  =
    loc_seg_fold (reverse_seg sg);
    loc_seg_fold sg;
    loc_seg_fold_f_comm a;
    Ll.fold_right_gtot_comm_permutation_t _ _ (loc_seg_fold_f #a)
                 M.loc_none (Ll.permutation_t_rev' sg.segment);
    L.rev_rev' sg.segment
