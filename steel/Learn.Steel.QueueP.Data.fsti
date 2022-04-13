module Learn.Steel.QueueP.Data

module L   = FStar.List.Pure
module G   = FStar.Ghost
module Mem = Steel.Memory

open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.ListP.Param
open Learn.Steel.ListP.Derived

noeq
type queue_st (r : Type) = {
  q_exit  : ref r;
  q_entry : ref r;
}

inline_for_extraction
type queue_t (p : list_param) = ref (queue_st p.r)

let rec last_cell (p : list_param) (l : list (cell_t p))
  : Tot (ref p.r) (decreases l)
  = match l with
    | []     -> null
    | [c]    -> c._1
    | _ :: tl -> last_cell p tl

type mqueue_sel_t (p : list_param) = list (cell_t p)

val mqueue_sl (p : list_param u#0) (q : queue_t p)
  : Mem.slprop u#1

val mqueue_sel (p : list_param) (q : queue_t p)
  : selector (mqueue_sel_t p) (mqueue_sl p q)

[@@__steel_reduce__]
let mqueue' (p : list_param) (q : queue_t p) : vprop' =
  {
    hp  = mqueue_sl    p q;
    t   = mqueue_sel_t p;
    sel = mqueue_sel   p q
  }
unfold let mqueue (p : list_param) (q : queue_t p) : vprop =
  VUnit (mqueue' p q)


[@@ __steel_reduce__]
let sel_queue (#vp:vprop) (p : list_param) (q : queue_t p)
  (h:rmem vp{FStar.Tactics.with_tactic selector_tactic (can_be_split vp (mqueue p q) /\ True)})
  : GTot (list (cell_t p))
  = h (mqueue p q)


val intro_mqueue (#opened:Mem.inames) (p : list_param) (q : queue_t p) (l_entry : ref p.r)
  : SteelGhost  unit opened
               (vptr q `star` mlistN p l_entry)
               (fun () -> mqueue p q)
               (requires fun h ->
                 let q_st = sel q h in
                 q_st.q_exit  == l_entry /\
                 q_st.q_entry == last_cell p (sel_listN p l_entry h))
               (ensures fun h0 () h1 ->
                 sel_queue p q h1 == sel_listN p l_entry h0)

val elim_mqueue (#opened:Mem.inames) (p : list_param) (q : queue_t p)
  : SteelGhost (G.erased (ref p.r)) opened
               (mqueue p q)
               (fun l_entry -> vptr q `star` mlistN p l_entry)
               (requires fun _ -> True)
               (ensures fun h0 l_entry h1 ->
                 let l = sel_listN p l_entry h1 in
                 sel q h1 == {
                   q_exit  = l_entry;
                   q_entry = last_cell p l
                 } /\
                 l == sel_queue p q h0)


let rec last_cell_not_null_lem (p : list_param) (l : list (cell_t p))
  : Lemma (requires Cons? l /\ L.for_all #(cell_t p) (fun c -> not (is_null c._1)) l)
          (ensures  is_null (last_cell p l) = false)
          (decreases l)
  = match l with
    | [last] -> ()
    | _ :: tl -> last_cell_not_null_lem p tl

let mqueue_inv_cases (p : list_param) (q_st : queue_st p.r) (l : mqueue_sel_t p) : prop
  = (q_st.q_exit ==  null /\ q_st.q_entry ==  null /\ l == []) \/
    (q_st.q_exit =!= null /\ q_st.q_entry =!= null /\ Cons? l)

let mqueue_inv_cases_lem (p : list_param) (q_st : queue_st p.r) (l : mlistN_sel_t p q_st.q_exit)
  : Lemma (requires q_st.q_entry == last_cell p l /\
                    L.for_all #(cell_t p) (fun c -> not (is_null c._1)) l)
          (ensures  mqueue_inv_cases p q_st l)
  = match l with
    | []   -> ()
    | _ :: _ -> last_cell_not_null_lem p l

let elim_mqueue_cases #opened (p : list_param) (q : queue_t p)
  : SteelGhost (G.erased (ref p.r)) opened
               (mqueue p q)
               (fun l_entry -> vptr q `star` mlistN p l_entry)
               (requires fun _ -> True)
               (ensures fun h0 l_entry h1 ->
                 let q_st = sel q h1 in
                 let l    = sel_listN p l_entry h1 in
                 q_st == {
                   q_exit  = l_entry;
                   q_entry = last_cell p l
                 } /\
                 l == sel_queue p q h0 /\
                 mqueue_inv_cases p q_st l)
  = 
    let l_entry = elim_mqueue p q in
    let q_st = gget (vptr q) in
    let l    = gget (mlistN p l_entry) in
    mlistN_cells_not_null p l_entry;
    mqueue_inv_cases_lem p q_st l;
    noop ();
    l_entry

let rec append_last_cell (p : list_param) (sg0 sg1 : list (cell_t p))
  : Lemma (requires Cons? sg1)
          (ensures  last_cell p L.(sg0@sg1) == last_cell p sg1)
          (decreases sg0)
  = match sg0 with
  | [] -> () | _ :: tl -> append_last_cell p tl sg1
