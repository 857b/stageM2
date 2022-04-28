module Learn.Steel.QueueP.Impl

module L = FStar.List.Pure
module G = FStar.Ghost

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.ListP.Param
open Learn.Steel.ListP.Derived
open Learn.Steel.ListP.Data
open Learn.Steel.QueueP.Data

#set-options "--fuel 3 --ifuel 1 --ide_id_info_off"

(* [malloc] *)

inline_for_extraction
let malloc (p : list_param) ()
  : Steel (queue_t p)
          emp (fun q -> mqueue p q)
          (requires fun _ -> True) (ensures fun _ q h -> sel_queue p q h == [])
  =
    (**) intro_mlistN_nil p null;
    let q = Steel.Reference.malloc #(queue_st p.r) ({q_exit = null; q_entry = null}) in
    (**) intro_mqueue p q null;
    return q

(* [free] *)

inline_for_extraction
let free (p : list_param) (q : queue_t p)
  : Steel unit
          (mqueue p q) (fun () -> emp)
          (requires fun h -> sel_queue p q h == []) (ensures fun _ _ _ -> True)
  =
    (**) let l_entry = elim_mqueue_cases p q in
    Steel.Reference.free q;
    (**) elim_mlistN_nil p l_entry

(* [is_empty] *)

inline_for_extraction
let is_empty (p : list_param) (q : queue_t p)
  : Steel bool
          (mqueue p q) (fun _ -> mqueue p q)
          (requires fun _ -> True)
          (ensures fun h0 b h1 -> frame_equalities (mqueue p q) h0 h1 /\
                               Nil? (sel_queue p q h0) <==> b)
  =
    (**) let l_entry = elim_mqueue_cases p q in
    let q_st = read q in
    (**) intro_mqueue p q l_entry;
    return (is_null q_st.q_exit)

(* [enqueue] *)

(* TODO? L.unsnoc *)
let rec unsnoc_queue (p : list_param) (l : list (cell_t p))
  : Pure (list (cell_t p) & cell_t p)
         (requires Cons? l)
         (ensures fun (ini, lt) -> l == L.(ini@[lt]) /\ L.length ini == L.length l - 1)
         (decreases l)
  = match l with
    | [lt] -> [], lt
    | hd :: tl -> let ini,lt = unsnoc_queue p tl in (hd :: ini, lt)

#push-options "--z3rlimit 20"
inline_for_extraction
let enqueue (p : list_param) (x : ref p.r) (q : queue_t p)
  : Steel  unit
          (vcell p x `star` mqueue p q) (fun () -> mqueue p q)
          (requires fun _ -> True)
          (ensures fun h0 () h1 -> sel_queue p q h1 == L.snoc (sel_queue p q h0, (|x, g_data p x h0|)))
  =
    (**) let h0 = get () in
    (**) let x_cell = G.hide (|x, g_data p x h0|) in
    (p.cell x).write_next null;
    (**) intro_mlist_sglt p x null;
    (**) let l_entry = elim_mqueue_cases p q in
    let q_st = read q in
    (**) let l = gget (mlistN p l_entry) in
    if is_null q_st.q_entry
    then begin
      (**) intro_mlistN p x 1;
      (**) elim_mlistN_nil p l_entry;
      write q ({q_exit = x; q_entry = x});
      (**) intro_mqueue p q x
    end else begin
      (**) let ini_lt = G.hide (unsnoc_queue p l) in
      (**) let ini = G.hide (fst ini_lt) in
      (**) let lt : G.erased (cell_t p) = G.hide (snd ini_lt) in
      (**) append_last_cell p ini [G.reveal lt];
      (**) assert (q_st.q_entry == (G.reveal lt)._1);
      (**) let len = elim_mlistN p l_entry in
      (**) let lt' = elim_mlist_append p l_entry len (len-1) (0+1) null ini [G.reveal lt] in
      (**) assert ((G.reveal lt)._1 == G.reveal lt');
      (**) let nil = elim_mlist_cons p lt' 0 null in
      (**) elim_mlist_nil p nil null;
      (**) change_equal_slprop (mlist p l_entry (len-1) lt'          `star` vcell p          lt')
      (**)                     (mlist p l_entry (len-1) q_st.q_entry `star` vcell p q_st.q_entry);
      (p.cell q_st.q_entry).write_next x;
      (**) intro_mlist_cons p q_st.q_entry x 1 null;
      (**) intro_mlist_append p l_entry (len-1) q_st.q_entry (1+1) null;
      (**) intro_mlistN p l_entry ((len-1)+(1+1));
      (**) append_last_cell p ini [G.reveal lt; G.reveal x_cell];
      (**) L.append_assoc ini [G.reveal lt] [G.reveal x_cell];
      let q_st = read q in
      write q ({q_st with q_entry = x});
      (**) intro_mqueue p q l_entry
    end
#pop-options

(* [dequeue] *)

inline_for_extraction
let dequeue (p : list_param) (q : queue_t p)
  : Steel (ref p.r)
          (mqueue p q) (fun x -> vcell p x `star` mqueue p q)
          (requires fun h0 -> Cons? (sel_queue p q h0))
          (ensures fun h0 x h1 -> sel_queue p q h0 == (|x, g_data p x h1|) :: sel_queue p q h1)
  =
    (**) let l_entry = elim_mqueue_cases p q in
    let q_st = read q in
    let rt = q_st.q_exit in
    (**) change_equal_slprop (mlistN p l_entry) (mlistN p rt);
    let nxt = listN_next p rt in
    (**) let h2 = get () in
    let q_st = read q in
    write q ({q_st with q_exit = nxt});
    if is_null nxt then begin
      (**) mlistN_entry_null_iff p nxt;
      let q_st = read q in
      write q ({q_st with q_entry = null});
      (**) intro_mqueue p q nxt
    end else begin
      (**) intro_mqueue p q nxt;
      (**) let h3 = get () in
      (**) assert (sel_queue p q h3 == sel_listN p nxt h2)
    end;
    return rt
