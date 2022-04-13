module Learn.Steel.QueueP.Data

module G  = FStar.Ghost
module US = Learn.Steel.Util

open Steel.Effect.Common
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.ListP.Param
open Learn.Steel.ListP.Derived


let mqueue_vp1 (p : list_param) (q_st : queue_st p.r)
  : vprop
  = mlistN p q_st.q_exit

unfold let mqueue_vp (p : list_param) (q : queue_t p)
  : vprop
  = vptr q `vdep` mqueue_vp1 p

let mqueue_ref (p : list_param) (q : queue_t p) ((|q_st, l|) : normal (t_of (mqueue_vp p q)))
  : prop
  = q_st.q_entry == last_cell p l

let mqueue_rew (p : list_param) (q : queue_t p) ((|_, l|) : normal (t_of (mqueue_vp p q)))
  : list (cell_t p)
  = l

unfold let mqueue0 (p : list_param) (q : queue_t p)
  : vprop
  = mqueue_vp p q
       `vrefine`  mqueue_ref p q
       `vrewrite` mqueue_rew p q

let mqueue_sl p q =
  let VUnit r = mqueue0 p q in r.hp

let mqueue_sel p q =
  let VUnit r = mqueue0 p q in r.sel

let mqueue_def p q : squash (mqueue p q == mqueue0 p q) = ()

let intro_mqueue #opened (p : list_param) (q : queue_t p) (l_entry : ref p.r)
  : SteelGhost  unit opened
               (vptr q `star` mlistN p l_entry)
               (fun () -> mqueue p q)
               (requires fun h ->
                 let q_st = sel q h in
                 q_st.q_exit  == l_entry /\
                 q_st.q_entry == last_cell p (sel_listN p l_entry h))
               (ensures fun h0 () h1 ->
                 sel_queue p q h1 == sel_listN p l_entry h0)
  =
    intro_vdep (vptr q) (mlistN p l_entry) (mqueue_vp1 p);
    intro_vrefine (mqueue_vp p q) (mqueue_ref p q);
    intro_vrewrite (mqueue_vp p q `vrefine` mqueue_ref p q) (mqueue_rew p q);
    US.rewrite_vprop (US.eq_sym (mqueue_def p q))

let elim_mqueue #opened (p : list_param) (q : queue_t p)
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
  =
    US.rewrite_vprop (mqueue_def p q);
    elim_vrewrite (mqueue_vp p q `vrefine` mqueue_ref p q) (mqueue_rew p q);
    elim_vrefine (mqueue_vp p q) (mqueue_ref p q);
    let q_st = elim_vdep (vptr q) (mqueue_vp1 p) in
    let rt   = q_st.q_exit in
    change_equal_slprop (mlistN p q_st.q_exit) (mlistN p rt);
    rt
