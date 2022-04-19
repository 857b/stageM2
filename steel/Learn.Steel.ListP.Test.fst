module Learn.Steel.ListP.Test

module U   = Learn.Util
module L   = FStar.List.Pure
module G   = FStar.Ghost
module Ll  = Learn.List
module US  = Learn.Steel.Util
module U32 = FStar.UInt32

open Steel.Effect
open Steel.Effect.Atomic
open Steel.Reference

open Learn.Steel.ListP

#set-options "--ide_id_info_off"

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

inline_for_extraction noextract
let p1' (ext : list_param_ext p1) : list_param
  = extend_list_param p1 ext

let rec p1_length (ext : list_param_ext p1) (r : ref cell1)
  : Steel  U32.t
          (mlistN (p1' ext) r) (fun _ -> mlistN (p1' ext) r)
          (requires fun h0        -> L.length (sel_listN (p1' ext) r h0) <= FStar.UInt.max_int U32.n)
          (ensures  fun h0 len h1 -> frame_equalities (mlistN (p1' ext) r) h0 h1 /\
                                  U32.v len = L.length (sel_listN (p1' ext) r h0))
  = length_body (p1' ext) (p1_length ext) r

inline_for_extraction
let p1_ext0 : list_param_ext p1 =
  fun _ -> {ext_vp = (fun _ -> emp); ext_data_t = ref U32.t; ext_data = (fun r _ -> r)}
inline_for_extraction
let p1_ext1 : list_param_ext p1 =
  fun _ -> { ext_vp = (fun r -> vptr r);
          ext_data_t = (ref U32.t & U32.t);
          ext_data = (fun r x -> (r,x))}

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
                  (rt <> 0ul ==> Cons? lv /\ (L.hd lv <: (x:ref cell1 & (ref U32.t & U32.t)))._2._2 == rt)))
  =
    let len = p1_length p1_ext1 l in
    if U32.(len >^ 0ul)
    then begin
      (**) let lv = gget (mlistN (p1' p1_ext1) l) in
      (**) let r1 = elim_mlistN_cons (p1' p1_ext1) l (L.hd lv) (L.tl lv) in
      (**) let g_ptr = elim_ext_cell p1_ext1 l in
      let cl = read l in 
      (**) assert (G.reveal g_ptr == cl.data_p);
      (**) change_equal_slprop (vptr g_ptr) (vptr cl.data_p);
      let rt = read cl.data_p in
      (**) intro_ext_cell p1_ext1 l (vptr cl.data_p);
      (**) intro_mlistN_cons (p1' p1_ext1) l r1;
      return rt
    end else return 0ul


(* ------------------------------------------------------------------- *)

module Mem = Steel.Memory

#push-options "--__no_positivity"
noeq
type cell2 = {
  next: ref cell2;
  data_b: ghost_ref bool;
  data_p: ref U32.t;
}
#pop-options

inline_for_extraction noextract
let p2_0 : list_param =
  list_param_of_vptr cell2 (ghost_ref bool & ref U32.t)
    ({get = (fun c -> c.next); set = (fun c x -> {c with next = x})})
    (fun c   -> (c.data_b, c.data_p))

noeq noextract
type p2_data_t = {
  ref_b : ghost_ref bool;
  ref_p : ref U32.t;
  p_val : option U32.t
}

[@@__ty_reduce__]
inline_for_extraction
let p2_ext : list_param_ext_r (ghost_ref bool & ref U32.t) = {
  ext_vp     = (fun (rs : ghost_ref bool & ref U32.t) ->
                  ghost_vptr rs._1 `vdep` (fun b -> US.vopt b (vptr rs._2)));
  ext_data_t = p2_data_t;
  ext_data   = (fun (ref_b, ref_p) (|_, p_val|) -> {ref_b;ref_p;p_val})
}

[@@__ty_reduce__]
inline_for_extraction noextract
let p2 = extend_list_param p2_0 (fun _ -> p2_ext)

let p2_data_extract (#opened : Mem.inames) (c : ref cell2) (rp : ref U32.t)
  : SteelGhost unit opened
      (vcell p2 c) (fun () -> vcell p2 c `star` vptr rp)
      (requires fun h0       -> let d0 = g_data p2 c h0 in
                             d0.ref_p == rp /\ Some? d0.p_val)
      (ensures  fun h0 () h1 -> g_next p2 c h1 == g_next p2 c h0 /\
                            (let d0 = g_data p2 c h0 in
                             Some? d0.p_val /\
                             g_data p2 c h1 == {d0 with p_val = None} /\
                             sel rp h1 == Some?.v d0.p_val))
 =
   let g_rs = elim_ext_cell (fun _ -> p2_ext) c in
   let (r_b, r_p) : ghost_ref bool & ref U32.t = G.reveal g_rs in
   assert_norm (p2_ext.ext_vp (r_b, r_p)
             == ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)));
   change_equal_slprop (p2_ext.ext_vp g_rs)
                       (ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)));
   let g_b = elim_vdep (ghost_vptr r_b) (fun b -> US.vopt b (vptr r_p)) in
   assert (g_b <: bool);
   US.vopt_elim_t (vptr r_p);
   change_equal_slprop (vptr r_p) (vptr rp);

   US.vopt_intro_f (vptr r_p);
   ghost_write r_b false;
   intro_vdep (ghost_vptr r_b)
              (US.vopt false (vptr r_p))
              (fun b -> US.vopt b (vptr r_p));
   intro_ext_cell (fun _ -> p2_ext) c 
                  (ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)))

let p2_data_insert (#opened : Mem.inames) (c : ref cell2) (rp : ref U32.t)
  : SteelGhost unit opened
      (vcell p2 c `star` vptr rp) (fun () -> vcell p2 c)
      (requires fun h0       -> let d0 = g_data p2 c h0 in
                             d0.ref_p == rp /\ None? d0.p_val)
      (ensures  fun h0 () h1 -> g_next p2 c h1 == g_next p2 c h0 /\
                            (let d0 = g_data p2 c h0 in
                             g_data p2 c h1 == {d0 with p_val = Some (sel rp h0)}))
 =
   let g_rs = elim_ext_cell (fun _ -> p2_ext) c in
   let (r_b, r_p) : ghost_ref bool & ref U32.t = G.reveal g_rs in
   assert_norm (p2_ext.ext_vp (r_b, r_p)
             == ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)));
   change_equal_slprop (p2_ext.ext_vp g_rs)
                       (ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)));
   let g_b = elim_vdep (ghost_vptr r_b) (fun b -> US.vopt b (vptr r_p)) in
   assert (not g_b);
   US.vopt_elim_f (vptr r_p);
   
   change_equal_slprop (vptr rp) (vptr r_p);
   US.vopt_intro_t (vptr r_p);
   ghost_write r_b true;
   intro_vdep (ghost_vptr r_b)
              (US.vopt true (vptr r_p))
              (fun b -> US.vopt b (vptr r_p));
   intro_ext_cell (fun _ -> p2_ext) c 
                  (ghost_vptr r_b `vdep` (fun b -> US.vopt b (vptr r_p)))


let rec p2_index (r : ref cell2) (len : G.erased nat) (exit : G.erased (ref cell2)) (i : U32.t)
  : Steel (ref cell2)
          (mlist p2 r len exit) (fun _ -> mlist p2 r len exit)
          (requires fun h -> U32.v i < len)
          (ensures  fun h rt h' -> U32.v i < len /\
                          frame_equalities (mlist p2 r len exit) h h' /\
                          rt == (L.index (sel_list p2 r len exit h) (U32.v i))._1)
  = index_body p2 p2_index r len exit i


(* TODO *)
noextract unfold
let normal_ty_steps =
   [delta_attr [`%__ty_reduce__];
    delta_only [`%Mklist_param?.cell;
                `%Mklist_param_r'?.cdata_t;
                `%Mklist_param_ext_r?.ext_data_t];
    iota]

inline_for_extraction noextract unfold
let normal_ty (#a:Type) (x:a) = norm normal_ty_steps x


#push-options "--ifuel 0"
let p2_data_extract_nth #opened (l : ref cell2) (len : nat) (exit : ref cell2) (i : nat) (r_p : ref U32.t)
  : SteelGhost unit opened
      (mlist p2 l len exit) (fun () -> mlist p2 l len exit `star` vptr r_p)
      (requires fun h0 -> i < len /\
                      (let d0 = (L.index (sel_list p2 l len exit h0) i)._2 in
                       d0.ref_p == r_p /\ Some? d0.p_val))
      (ensures fun h0 () h1 ->
                       i < len /\
                      (let l0 = sel_list p2 l len exit h0 in
                       let cl0 = L.index l0 i in
                       let ri = cl0._1 in let d0 = cl0._2 in
                       sel_list p2 l len exit h1 == Ll.set i ((|ri, {d0 with p_val = None}|)) l0 /\
                       Some? d0.p_val /\
                       sel r_p h1 == Some?.v d0.p_val))
  =
    let lv : G.erased (mlist_sel_t p2 l len exit) = gget (mlist p2 l len exit) in
    let (|r_i,d0|) : x:ref cell2 & data_t p2 x = L.index lv i in
    let d1  = {U.cast p2_data_t d0 with p_val = None} in
    mlist_gmap_at p2 l len exit i r_i d0 d1
      emp (vptr r_p) (fun (_ : t_of emp) -> True) (fun (_ : t_of emp) (x : U32.t) -> x == Some?.v d0.p_val)
      (fun () -> p2_data_extract r_i r_p)

let p2_data_insert_nth #opened (l : ref cell2) (len : nat) (exit : ref cell2) (i : nat) (rpi : ref U32.t)
  : SteelGhost unit opened
      (mlist p2 l len exit `star` vptr rpi) (fun () -> mlist p2 l len exit)
      (requires fun h0 -> i < len /\
                      (let d0 = (L.index (sel_list p2 l len exit h0) i)._2 in
                       d0.ref_p == rpi /\ None? d0.p_val))
      (ensures fun h0 () h1 ->
                       i < len /\
                      (let l0 = sel_list p2 l len exit h0 in
                       let cl0 = L.index l0 i in
                       let ri = cl0._1 in let d0 = cl0._2 in
                       sel_list p2 l len exit h1
                         == Ll.set i ((|ri, {d0 with p_val = Some (sel rpi h0)}|)) l0))
  =
    let lv : G.erased (mlist_sel_t p2 l len exit) = gget (mlist p2 l len exit) in
    let x  : G.erased U32.t = gget (vptr rpi) in
    let (|r_i,d0|) : x:ref cell2 & data_t p2 x = L.index lv i in
    let d1  = {U.cast p2_data_t d0 with p_val = Some (G.reveal x)} in
    mlist_gmap_at p2 l len exit i r_i d0 d1
      (vptr rpi) emp (fun x' -> x' == G.reveal x) (fun _ _ -> True)
      (fun () -> p2_data_insert r_i rpi)


inline_for_extraction noextract
let p2_extract_index (l : ref cell2) (len : G.erased nat) (exit : G.erased (ref cell2)) (i : U32.t)
  : Steel (ref U32.t)
      (mlist p2 l len exit) (fun r_p -> mlist p2 l len exit `star` vptr r_p)
      (requires fun h0 -> U32.v i < len /\
                       Some? (L.index (sel_list p2 l len exit h0) (U32.v i))._2.p_val)
      (ensures fun h0 r_p h1 ->
                       U32.v i < len /\
                      (let l0  = sel_list p2 l len exit h0 in
                       let cl0 = L.index l0 (U32.v i) in
                       let ri = cl0._1 in let d0 = cl0._2 in
                       r_p == d0.ref_p /\
                       sel_list p2 l len exit h1
                         == Ll.set (U32.v i) ((|ri, {d0 with p_val = None}|)) l0 /\
                       Some? d0.p_val /\
                       sel r_p h1 == Some?.v d0.p_val))
  =
    let r  = p2_index l len exit i in
    (**) let ex = mlist_extract p2 l len exit (U32.v i) in
    (**) change_equal_slprop (vcell p2 ex.r) (vcell p2 r);
    (**) let g_rs = elim_ext_cell #p2_0 (fun _ -> p2_ext) r in
    let cl  = read r in
    let r_p = cl.data_p in
    (**) intro_ext_cell #p2_0 (fun _ -> p2_ext) r (p2_ext.ext_vp g_rs);
    (**) p2_data_extract r r_p;
    (**) change_equal_slprop (vcell p2 r) (vcell p2 ex.r);
    (**) ex.close ();
    return r_p
#pop-options

let test_p2 (l : ref cell2) (len : G.erased nat) (exit : G.erased (ref cell2)) (i0 i1 : U32.t)
  : Steel unit
      (mlist p2 l len exit) (fun () -> mlist p2 l len exit)
      (requires fun h0 -> U32.v i0 < len /\ U32.v i1 < len /\ U32.(v i0 <> v i1) /\
                      (let l0 = sel_list p2 l len exit h0 in
                       Some? (L.index l0 (U32.v i0))._2.p_val /\
                       Some? (L.index l0 (U32.v i1))._2.p_val))
      (ensures fun h0 () h1 ->
                       U32.v i0 < len /\ U32.v i1 < len /\
                      (let l0 = sel_list p2 l len exit h1 in
                       Some? (L.index l0 (U32.v i0))._2.p_val /\
                       Some? (L.index l0 (U32.v i1))._2.p_val))
  =
    let r0 = p2_extract_index l len exit i0 in
    let r1 = p2_extract_index l len exit i1 in
    write r0 0ul;
    write r1 1ul;
    (* TODO: extract
    let _ = par
      (fun () -> (write r0 0ul <: SteelT unit (vptr r0) (fun () -> vptr r0)))
      (fun () -> (write r1 1ul <: SteelT unit (vptr r1) (fun () -> vptr r1))) in
     *)
    (**) p2_data_insert_nth l len exit (U32.v i0) r0;
    (**) p2_data_insert_nth l len exit (U32.v i1) r1
