module Learn.Steel.DLList.Param

module Mem = Steel.Memory

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference


type direction =
  | Forward
  | Backward

noeq inline_for_extraction
type list_param_r' (r : Type) = {
  vp       : vprop;
  cdata_t  : Type;
  get_ref  : normal (t_of vp) -> direction -> GTot (ref r);
  set_ref  : normal (t_of vp) -> (d : direction) -> (x : ref r) -> GTot (c : normal (t_of vp) { get_ref c d == x });
  get_data : normal (t_of vp) -> GTot (normal cdata_t);

  read_ref  : (d : direction) ->
              Steel (ref r) vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 x h1 -> frame_equalities vp h0 h1 /\ x == get_ref (h0 vp) d);
  write_ref : (d : direction) -> (x : ref r) ->
              Steel unit vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 () h1 -> h1 vp == set_ref (h0 vp) d x)
}

inline_for_extraction noextract
type list_param_r (r : Type) = p:list_param_r' r {
  (forall (s : normal (t_of p.vp)) (d d' : direction) (x:ref r) . {:pattern (p.get_ref (p.set_ref s d x) d')}
     d <> d' ==> p.get_ref (p.set_ref s d x) d' == p.get_ref s d') /\
  (forall (s : normal (t_of p.vp)) (d : direction) (x:ref r) . {:pattern (p.get_data (p.set_ref s d x))}
     p.get_data (p.set_ref s d x) == p.get_data s)
}

noeq inline_for_extraction
type list_param = {
  r      : Type;
  cell   : ref r -> list_param_r r;
  nnull  : (x : ref r) -> (m : Mem.mem) ->
           Lemma (requires Mem.interp (hp_of (cell x).vp) m)
                 (ensures  is_null x == false)
}

let data_t (p : list_param) (x : ref p.r) : Type = (p.cell x).cdata_t
let cell_t (p : list_param) : Type = dtuple2 (ref p.r) (data_t p)

unfold let vcell (p:list_param) (x:ref p.r)
  : vprop
  = (p.cell x).vp

[@@ __steel_reduce__]
let g_cref (#q:vprop) (p:list_param) (d : direction) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (ref p.r)
  = (p.cell x).get_ref (h (vcell p x)) d

[@@ __steel_reduce__]
let g_data (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (data_t p x)
  = (p.cell x).get_data (h (vcell p x))

[@@ __steel_reduce__]
let g_cell (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (cell_t p)
  = (|x, g_data p x h|)

let list_cell_not_null #opened (p : list_param) (x:ref p.r)
  : SteelGhost unit opened (vcell p x) (fun () -> (vcell p x))
              (requires fun _ -> True)
              (ensures fun h0 () h1 -> frame_equalities (vcell p x) h0 h1 /\
                                    is_null x = false)
  = extract_info_raw (vcell p x) (is_null x == false) (p.nnull x)
