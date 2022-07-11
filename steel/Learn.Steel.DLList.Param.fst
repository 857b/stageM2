module Learn.Steel.DLList.Param

module Mem = Steel.Memory

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference


(*** Definition *)

noeq inline_for_extraction noextract
type cell_r (r : Type) (d : Type) = {
  cl_prv  : ref r;
  cl_nxt  : ref r;
  cl_data : d;
}

noeq inline_for_extraction
type list_param_r (r : Type) = {
  vp       : vprop;
  cdata_t  : Type;
  cl_f     : normal (t_of vp) -> GTot (cell_r r cdata_t);

  read_prv  : unit ->
              Steel (ref r) vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 x h1 -> frame_equalities vp h0 h1 /\ x == (cl_f (h0 vp)).cl_prv);
  read_nxt  : unit ->
              Steel (ref r) vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 x h1 -> frame_equalities vp h0 h1 /\ x == (cl_f (h0 vp)).cl_nxt);
  write_prv : (cl_prv : ref r) ->
              Steel unit vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 () h1 -> cl_f (h1 vp) == {cl_f (h0 vp) with cl_prv});
  write_nxt : (cl_nxt : ref r) ->
              Steel unit vp (fun _ -> vp) (requires fun _ -> True)
                (ensures fun h0 () h1 -> cl_f (h1 vp) == {cl_f (h0 vp) with cl_nxt});
}

noeq inline_for_extraction
type list_param = {
  r      : Type;
  cell   : ref r -> list_param_r r;
  nnull  : (x : ref r) -> (m : Mem.mem) ->
           Lemma (requires Mem.interp (hp_of (cell x).vp) m)
                 (ensures  is_null x == false)
}


(*** Derived *)

let data_t  (p : list_param) (x : ref p.r) : Type = (p.cell x).cdata_t
let cell_t  (p : list_param) (x : ref p.r) : Type = cell_r p.r (data_t p x)
let rcell_t (p : list_param) : Type = dtuple2 (ref p.r) (data_t p)

unfold let vcell (p:list_param) (x:ref p.r)
  : vprop
  = (p.cell x).vp

[@@ __steel_reduce__]
let g_cl (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (cell_t p x)
  = (p.cell x).cl_f (h (vcell p x))

[@@ __steel_reduce__]
let g_rcell (#q:vprop) (p:list_param) (x:ref p.r)
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (vcell p x) /\ True)})
  : GTot (rcell_t p)
  = (|x, (g_cl p x h).cl_data|)

let gget_cl #opened (p : list_param) (x : ref p.r)
  : SteelGhost (Ghost.erased (cell_t p x)) opened (vcell p x) (fun _ -> vcell p x)
      (requires fun _ -> True)
      (ensures  fun h0 c h1 -> frame_equalities (vcell p x) h0 h1 /\
                            Ghost.reveal c == g_cl p x h0)
  =
    let c = gget (vcell p x) in
    (p.cell x).cl_f c

let list_cell_not_null #opened (p : list_param) (x:ref p.r)
  : SteelGhost unit opened (vcell p x) (fun () -> vcell p x)
              (requires fun _ -> True)
              (ensures fun h0 () h1 -> frame_equalities (vcell p x) h0 h1 /\
                                    is_null x = false)
  = extract_info_raw (vcell p x) (is_null x == false) (p.nnull x)


(*** Building a [list_param] *)

inline_for_extraction
let list_param_of_vptr
      (c cdata_t : Type) (cl_f : c -> Tot (cell_r c cdata_t))
      (set_prv : (x : c) -> (cl_prv : ref c) -> (y : c {cl_f y == {cl_f x with cl_prv}}))
      (set_nxt : (x : c) -> (cl_nxt : ref c) -> (y : c {cl_f y == {cl_f x with cl_nxt}}))
  : list_param
  = {
    r    = c;
    cell = (fun (r : ref c) -> {
        vp = vptr r;
        cdata_t;
        cl_f;
        read_prv  = (fun () -> let s = read r in (cl_f s).cl_prv);
        read_nxt  = (fun () -> let s = read r in (cl_f s).cl_nxt);
        write_prv = (fun x  -> let s = read r in write r (set_prv s x));
        write_nxt = (fun x  -> let s = read r in write r (set_nxt s x));
      });
    nnull = (fun r m -> ptrp_sel_interp r full_perm m;
                     pts_to_not_null r full_perm (ptrp_sel r full_perm m) m);
  }
