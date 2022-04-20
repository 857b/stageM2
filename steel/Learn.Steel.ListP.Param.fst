module Learn.Steel.ListP.Param

module G   = FStar.Ghost
module US  = Learn.Steel.Util
module Mem = Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

#set-options "--ide_id_info_off"

(* TODO *)
irreducible let __ty_reduce__ : unit = ()

/// [list_param] is a parameter used to represent the cells of a linked list.
/// It is a collection of vprop indexed by a reference type. Each vprop has a selector that can be decomposed
/// into two part:
/// - A next field that is used by the linked-list. An instance must provide a getter and a setter for this field
///   on the selector type and Steel functions to read and change its value.
/// - A data field that is unchanged by the functions operating on abstract linked list. We only require a getter
///   and that it is not affected by updates of the next field.

noeq inline_for_extraction noextract
type list_param_r' (r : Type) = {
  vp        : vprop;
  cdata_t   : Type;
  get_next  : normal (t_of vp) -> GTot (ref r);
  set_next  : normal (t_of vp) -> (nxt:ref r) -> GTot (c:normal (t_of vp) {get_next c == nxt});
  get_data  : normal (t_of vp) -> GTot (normal cdata_t);

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

noeq inline_for_extraction
type list_param = {
  r      : Type;
  cell   : ref r -> list_param_r r;
  nnull  : (x : ref r) -> (m : Mem.mem) ->
           Lemma (requires Mem.interp (hp_of (cell x).vp) m)
                 (ensures  is_null x == false)
}

[@@__ty_reduce__]
let data_t (p : list_param) (x : ref p.r) : Type = (p.cell x).cdata_t
[@@__ty_reduce__]
let cell_t (p : list_param) : Type = dtuple2 (ref p.r) (data_t p)

inline_for_extraction noextract
let aptr_next (p : list_param) (x : ref p.r) : US.aptr (ref p.r) = {
  vp      = (p.cell x).vp;
  of_sel  = (p.cell x).get_next;
  set_sel = (p.cell x).set_next;
  read    = (p.cell x).read_next;
  write   = (p.cell x).write_next
}

unfold let vcell (p:list_param) (x:ref p.r)
  : vprop
  = (p.cell x).vp

[@@ __steel_reduce__]
let g_next (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (ref p.r)
  = (p.cell x).get_next (h (vcell p x))

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


/// [list_param_of_vptr] builds a [list_param] for the common case where the cells are [vptr].
inline_for_extraction noextract
let list_param_of_vptr (c cdata_t : Type)
    (gs_next : US.get_set_t c (ref c)) (get_data : c -> cdata_t)
  : Pure list_param
    (requires forall (s : c) (x:ref c) . {:pattern (get_data (gs_next.set s x))}
                get_data (gs_next.set s x) == get_data s)
    (ensures fun _ -> True)
  = {
    r    = c;
    cell = (fun (r : ref c) -> {
              vp = vptr r;
              cdata_t;
              get_next = gs_next.get;
              set_next = (fun s x -> gs_next.set s x);
              get_data;
              read_next  = (fun () -> let s = read r in gs_next.get s);
              write_next = (fun x  -> let s = read r in write r (gs_next.set s x))
           });
    nnull = (fun r m -> ptrp_sel_interp r full_perm m;
                     pts_to_not_null r full_perm (ptrp_sel r full_perm m) m)
  }


(** [extend_list_param] : extending the vprop of a list_param *)
(* TODO? hide *)

/// [extend_list_param] allows to extends the cells of a [list_param] with vprops that depends only on the abstract
/// data field of the cell. This extension is erasable so a function that operate on linked lists with parameter
/// [extend_list_param p e] need to be extracted only once for each [p].

[@@erasable]
noeq inline_for_extraction
type list_param_ext_r (d0 : Type) = {
  ext_vp     : d0 -> vprop;
  ext_data_t : Type;
  ext_data   : (x:d0) -> normal (t_of (ext_vp x)) -> GTot ext_data_t (* TODO? (x:d0 & ...) -> ... *)
}

type list_param_ext (p : list_param) : Type = (r : ref p.r) -> list_param_ext_r (data_t p r)

let extend_list_param_vp1 (#r : Type) (p : list_param_r r) (e : list_param_ext_r p.cdata_t) (x : t_of (p.vp))
  : vprop
  = e.ext_vp (p.get_data x)

[@@__ty_reduce__]
inline_for_extraction noextract
let extend_list_param_r (r : Type) (p : list_param_r r) (e : list_param_ext_r p.cdata_t)
  : list_param_r r = {
  vp         = p.vp `vdep` extend_list_param_vp1 p e;
  cdata_t    = e.ext_data_t;
  get_next   = (fun (|x, y|) -> p.get_next x);
  set_next   = (fun (|x, y|) nxt -> (|p.set_next x nxt, y|));
  get_data   = (fun (|x, y|) -> e.ext_data (p.get_data x) y);
  read_next  = (fun () ->
                  (**) let sl = elim_vdep p.vp (extend_list_param_vp1 p e) in
                  let rt = p.read_next () in
                  (**) intro_vdep p.vp (e.ext_vp (p.get_data sl)) (extend_list_param_vp1 p e);
                  return rt);
  write_next = (fun nxt ->
                  (**) let sl = elim_vdep p.vp (extend_list_param_vp1 p e) in
                  p.write_next nxt;
                  (**) intro_vdep p.vp (e.ext_vp (p.get_data sl)) (extend_list_param_vp1 p e));
}

[@@__ty_reduce__]
inline_for_extraction noextract
let extend_list_param (p : list_param) (e : list_param_ext p)
  : list_param = {
  r     = p.r;
  cell  = (fun (x : ref p.r) -> extend_list_param_r p.r (p.cell x) (e x));
  nnull = (fun (x : ref p.r) (m : Mem.mem) ->
             interp_vdep_hp (p.cell x).vp (extend_list_param_vp1 (p.cell x) (e x)) m;
             p.nnull x m)
}

let intro_ext_cell (#p : list_param) #opened (e : list_param_ext p) (r : ref p.r)
                   (q : vprop)
  : SteelGhost unit opened
      (vcell p r `star` q) (fun () -> vcell (extend_list_param p e) r)
      (requires fun h0 -> q == (e r).ext_vp (g_data p r h0))
      (ensures  fun h0 () h1 ->
        q == (e r).ext_vp (g_data p r h0) /\
        g_data (extend_list_param p e) r h1
          == (e r).ext_data (g_data p r h0) (h0 q) /\
        g_next (extend_list_param p e) r h1
          == g_next p r h0)
  =
    intro_vdep (vcell p r) q (extend_list_param_vp1 (p.cell r) (e r))

let elim_ext_cell (#p : list_param) #opened (e : list_param_ext p) (r : ref p.r)
  : SteelGhost (G.erased (data_t p r)) opened
      (vcell (extend_list_param p e) r) (fun dt -> vcell p r `star` (e r).ext_vp dt)
      (requires fun _ -> True)
      (ensures  fun h0 dt h1 ->
         G.reveal dt == g_data p r h1 /\
         g_data (extend_list_param p e) r h0
           == (e r).ext_data dt (h1 ((e r).ext_vp dt)) /\
         g_next (extend_list_param p e) r h0
           == g_next p r h1)
  =
    let sl = elim_vdep (vcell p r) (extend_list_param_vp1 (p.cell r) (e r)) in
    let dt : G.erased (data_t p r) = (p.cell r).get_data sl in
    change_equal_slprop (extend_list_param_vp1 (p.cell r) (e r) sl)
                        ((e r).ext_vp dt);
    dt
