module Learn.Steel.ListP.Test

module L   = FStar.List.Pure
module G   = FStar.Ghost
module US  = Learn.Steel.Util
module U32 = FStar.UInt32

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.ListP

#push-options "--__no_positivity"
noeq
type cell0 = {
  next: ref cell0;
  data_x: U32.t;
  data_y: bool
}
#pop-options

inline_for_extraction noextract
let p0 : list_param =
  list_param_of_vptr cell0 (U32.t & bool)
    ({get = (fun c -> c.next); set = (fun c x -> {c with next = x})})
    (fun c   -> (c.data_x, c.data_y))

let rec p0_length (r : ref cell0)
  : Steel  U32.t
          (mlistN p0 r) (fun _ -> mlistN p0 r)
          (requires fun h0        -> L.length (sel_listN p0 r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN p0 r) h0 h1 /\
                                  U32.v len = L.length (sel_listN p0 r h0))
  = length_body p0 p0_length r

noextract
let p0_reverse (r : ref cell0)
  : Steel (ref cell0)
          (mlistN p0 r) (fun rt -> mlistN p0 rt)
          (requires fun _ -> True)
          (ensures fun h0 rt h1 -> sel_listN p0 rt h1 == L.rev (sel_listN p0 r h0))
  = reverse p0 r


(* ------------------------------------------------------------------- *)

#push-options "--__no_positivity"
noeq
type cell1 = {
  next: ref cell1;
  data_p: ref U32.t
}
#pop-options

inline_for_extraction noextract
let p1 : list_param =
  list_param_of_vptr cell1 (ref U32.t)
    ({get = (fun c -> c.next); set = (fun c x -> {c with next = x})})
    (fun c   -> c.data_p)

noextract
type p1_ext = (r : ref cell1) -> ref U32.t -> vprop

inline_for_extraction noextract
let p1' (ext : p1_ext) : list_param
  = extend_list_param p1 ext

let rec p1_length (ext : p1_ext) (r : ref cell1)
  : Steel  U32.t
          (mlistN (p1' ext) r) (fun _ -> mlistN (p1' ext) r)
          (requires fun h0        -> L.length (sel_listN (p1' ext) r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN (p1' ext) r) h0 h1 /\
                                  U32.v len = L.length (sel_listN (p1' ext) r h0))
  = length_body (p1' ext) (p1_length ext) r

noextract
let p1_ext0 : p1_ext = fun _ _ -> emp
noextract
let p1_ext1 : p1_ext = fun _ r -> vptr r

let test_p1_ext0 (l : ref cell1)
  : Steel bool (mlistN (p1' p1_ext0) l) (fun _ -> mlistN (p1' p1_ext0) l)
               (requires fun h0 -> L.length (sel_listN (p1' p1_ext0) l h0) <= FStar.UInt.max_int U32.n)
               (ensures  fun _ _ _ -> True)
  =
    let len = p1_length p1_ext0 l in
    U32.(len >^ 0ul)

let test_p1_ext1 (l : ref cell1)
  : Steel U32.t (mlistN (p1' p1_ext1) l) (fun _ -> mlistN (p1' p1_ext1) l)
                (requires fun h0    -> L.length (sel_listN (p1' p1_ext1) l h0) <= FStar.UInt.max_int U32.n)
                (ensures  fun h0 rt h1 ->
                  frame_equalities (mlistN (p1' p1_ext1) l) h0 h1 /\
                 (let lv = sel_listN (p1' p1_ext1) l h0 in
                  (rt <> 0ul ==> Cons? lv /\ (L.hd lv)._2._2 == rt)))
  =
    let len = p1_length p1_ext1 l in
    if U32.(len >^ 0ul)
    then begin
      (**) let lv = gget (mlistN (p1' p1_ext1) l) in
      (**) let r1 = elim_mlistN_cons (p1' p1_ext1) l (L.hd lv) (L.tl lv) in
      (**) let g_cl = elim_vdep (vptr l) (extend_list_param_vp1 (p1.cell l) (p1_ext1 l)) in
      let cl = read l in 
      (**) assert (G.reveal g_cl == cl);
      (**) change_equal_slprop (vptr g_cl.data_p) (vptr cl.data_p);
      let rt = read cl.data_p in
      (**) intro_vdep (vptr l) (vptr cl.data_p) (extend_list_param_vp1 (p1.cell l) (p1_ext1 l));
      (**) intro_mlistN_cons (p1' p1_ext1) l r1;
      return rt
    end else return 0ul


(* ------------------------------------------------------------------- *)

#push-options "--__no_positivity"
noeq
type cell2 = {
  next: ref cell2;
  data_b: ghost_ref bool;
  data_p: ref U32.t;
}
#pop-options

(* TODO? [@@ erasable] on list_param *)
inline_for_extraction noextract
let p2_0 : list_param =
  list_param_of_vptr cell2 (ghost_ref bool & ref U32.t)
    ({get = (fun c -> c.next); set = (fun c x -> {c with next = x})})
    (fun c   -> (c.data_b, c.data_p))

noextract
let p2_ext ((b, p) : (ghost_ref bool & ref U32.t)) : vprop =
  ghost_vptr b `vdep` (fun b -> US.vopt b (vptr p))

inline_for_extraction noextract
let p2 = extend_list_param p2_0 (fun _ -> p2_ext)

(* TODO
assume
val extract_data_p (#opened : Mem.inames) (c : ref cell2) (rp : ref U32.t)
  : unit -> SteelGhost unit opened
      (vcell p2 c) (fun () -> vcell p2 c `star` vptr rp)
      (requires fun h0       -> let (|(_, rp'), (|b, _|)|) = g_data p2 c h0 in
                             (b <: bool) /\ rp' == rp)
      (ensures  fun h0 () h1 -> g_next p2 c h1 == g_next p2 c h0 /\
                            (let (|(rb, rp'), _|) = g_data p2 c h0 in
                             g_data p2 c h1 == (|(rb, rp'), (|false, None #U32.t|)|)))

let test_p2 (l : ref cell2) (len : G.erased nat) (r1 : ref U32.t)
  : Steel unit (mlist p2 l len null) (fun () -> mlist p2 l len null `star` vptr r1)
               (requires fun h0 -> len >= 2 /\
                               (let (|_, (|(_,r1'), (|b, _|)|)|) = L.index (sel_list p2 l len null h0) 1
                                in (b <: bool) /\ r1' == r1))
               (ensures fun h0 () h1 -> True)
  =
    let lv : G.erased (mlist_sel_t p2 l len null) = gget (mlist p2 l len null) in
    let d0_r = G.hide (L.index lv 1)._1 in
    let d0   = G.hide ((L.index lv 1)._2
                      <: dtuple2 (ghost_ref bool & ref U32.t) (fun (_,_) -> (_:bool & option U32.t)) )in
    mlist_gmap_at p2 l len null 1 (L.index lv 1)._1 d0 (|dfst (G.reveal d0), (|false, None #U32.t|)|)
      emp (vptr r1) (fun (_ : t_of emp) -> True) (fun _ -> True)
      (extract_data_p (L.index lv 1)._1 r1)
*)
