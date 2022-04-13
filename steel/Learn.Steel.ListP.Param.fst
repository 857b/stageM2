module Learn.Steel.ListP.Param

module US  = Learn.Steel.Util
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference


noeq inline_for_extraction noextract
type list_param_r' (r : Type) = {
  vp        : vprop;
  data_t    : Type;
  get_next  : normal (t_of vp) -> GTot (ref r);
  set_next  : normal (t_of vp) -> (nxt:ref r) -> GTot (c:normal (t_of vp) {get_next c == nxt});
  get_data  : normal (t_of vp) -> GTot data_t;

  read_next  : unit -> Steel (ref r) vp (fun _ -> vp) (requires fun _ -> True)
                      (ensures fun h0 x h1 -> frame_equalities vp h0 h1 /\ x == get_next (h0 vp));
  write_next : (x : ref r) -> Steel unit vp (fun _ -> vp) (requires fun _ -> True)
                      (ensures fun h0 () h1 -> h1 vp == set_next (h0 vp) x)
}

inline_for_extraction noextract
type list_param_r (r : Type) = p:list_param_r' r {
  (forall (s : normal (t_of p.vp)) (x0 x1 : ref r) . {:pattern (p.set_next (p.set_next s x0) x1)}
      p.set_next (p.set_next s x0) x1 == p.set_next s x1) /\
  (forall (s : normal (t_of p.vp)) . {:pattern (p.set_next s (p.get_next s))}
      p.set_next s (p.get_next s) == s) /\
  (forall (s : normal (t_of p.vp)) (x:ref r) . {:pattern (p.get_data (p.set_next s x))}
     p.get_data (p.set_next s x) == p.get_data s)
}

noeq inline_for_extraction noextract
type list_param = {
  r      : Type;
  cell   : ref r -> list_param_r r;
  nnull  : (x : ref r) -> (m : Mem.mem) ->
           Lemma (requires Mem.interp (hp_of (cell x).vp) m)
                 (ensures  is_null x == false)
}

let cell_t (p : list_param) : Type = x:ref p.r & (p.cell x).data_t

inline_for_extraction noextract
let aptr_next (p : list_param) (x : ref p.r) : US.aptr (ref p.r) = {
  vp      = (p.cell x).vp;
  of_sel  = (p.cell x).get_next;
  set_sel = (p.cell x).set_next;
  read    = (p.cell x).read_next;
  write   = (p.cell x).write_next
}

[@@ __steel_reduce__]
let g_next (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (p.cell x).vp /\ True)})
  : GTot (ref p.r)
  = (p.cell x).get_next (h (p.cell x).vp)

[@@ __steel_reduce__]
let g_data (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (p.cell x).vp /\ True)})
  : GTot ((p.cell x).data_t)
  = (p.cell x).get_data (h (p.cell x).vp)

let list_cell_not_null #opened (p : list_param) (x:ref p.r)
  : SteelGhost unit opened (p.cell x).vp (fun () -> (p.cell x).vp)
              (requires fun _ -> True)
              (ensures fun h0 () h1 -> frame_equalities (p.cell x).vp h0 h1 /\
                                    is_null x = false)
  = extract_info_raw (p.cell x).vp (is_null x == false) (p.nnull x)


inline_for_extraction noextract
let list_param_of_vptr (c data_t : Type)
    (gs_next : US.get_set_t c (ref c)) (get_data : c -> data_t)
  : Pure list_param
    (requires forall (s : c) (x:ref c) . {:pattern (get_data (gs_next.set s x))}
                get_data (gs_next.set s x) == get_data s)
    (ensures fun _ -> True)
  = {
    r    = c;
    cell = (fun (r : ref c) -> {
              vp = vptr r;
              data_t;
              get_next = gs_next.get;
              set_next = (fun s x -> gs_next.set s x);
              get_data;
              read_next  = (fun () -> let s = read r in gs_next.get s);
              write_next = (fun x  -> let s = read r in write r (gs_next.set s x))
           });
    nnull = (fun r m -> ptrp_sel_interp r full_perm m;
                     pts_to_not_null r full_perm (ptrp_sel r full_perm m) m)
  }
