module Learn.Steel.ListP.Impl

module L   = FStar.List.Pure
module G   = FStar.Ghost
module US  = Learn.Steel.Util
module U32 = FStar.UInt32
module Loops = Steel.Loops (* Not yet extracted by krml ? *)

open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

open Learn.Steel.ListP.Param
open Learn.Steel.ListP.Data
open Learn.Steel.ListP.Derived

#set-options "--fuel 3 --ifuel 1"

(* [length] *)

let length_ty (p : list_param) : Type = (r : ref p.r) ->
  Steel  U32.t
        (mlistN p r) (fun _ -> mlistN p r)
        (* TODO? move as ==> in ensures *)
        (requires fun h0        -> L.length (sel_listN p r h0) <= FStar.UInt.max_int U32.n)
        (ensures  fun h0 len h1 -> frame_equalities (mlistN p r) h0 h1 /\
                                U32.v len = L.length (sel_listN p r h0))

inline_for_extraction noextract
let length_body (p : list_param) ($rec_f : length_ty p) : length_ty p
  = fun r ->
    let b = listN_is_nil p r in
    if b
    then return 0ul
    else begin
      let r'   = listN_next p r in
      let len' = rec_f r'       in
      (**) intro_mlistN_cons p r r';
      return U32.(len' +^ 1ul)
    end

(* [reverse] *)

unfold let reverse_inv_vp1 (p : list_param) (rs : ref p.r & ref p.r) : vprop =
  mlistN p rs._1 `star` mlistN p rs._2

let reverse_inv_ref (p : list_param) (trg : list (cell_t p)) (b : G.erased bool)
  (s : (rs : (ref p.r & ref p.r) & (mlistN_sel_t p rs._1 & mlistN_sel_t p rs._2)))
  : prop =
  trg == L.rev_acc s._2._1 s._2._2 /\ is_null s._1._1 = not (G.reveal b)

let reverse_inv (p : list_param) (trg : list (cell_t p)) (it_f it_r : ref (ref p.r))
                (b : G.erased bool) : vprop =
  vrefine ((vptr it_f `star` vptr it_r) `vdep` reverse_inv_vp1 p)
          (reverse_inv_ref p trg b)

let intro_reverse_inv #opened (p : list_param) trg it_f it_r (b : G.erased bool) (r_f r_r : ref p.r)
  : SteelGhost unit opened
              (vptr it_f `star` vptr it_r `star` mlistN p r_f `star` mlistN p r_r)
              (fun () -> reverse_inv p trg it_f it_r b)
              (requires fun h -> sel it_f h == r_f /\ sel it_r h == r_r /\
                              trg == L.rev_acc (sel_listN p r_f h) (sel_listN p r_r h) /\
                              is_null r_f = not (G.reveal b))
              (ensures fun _ _ _ -> True)
  =
    intro_vdep (vptr it_f `star` vptr it_r)
               (mlistN p r_f `star` mlistN p r_r)
               (reverse_inv_vp1 p);
    intro_vrefine ((vptr it_f `star` vptr it_r) `vdep` reverse_inv_vp1 p)
                  (reverse_inv_ref p trg b)

let elim_reverse_inv #opened (p : list_param) (trg : list (cell_t p)) (it_f it_r : ref (ref p.r))
                             (b : G.erased bool)
  : SteelGhost (G.erased (ref p.r & ref p.r)) opened
               (reverse_inv p trg it_f it_r b)
               (fun rs -> vptr it_f `star` vptr it_r `star` reverse_inv_vp1 p rs)
               (requires fun _ -> True)
               (ensures fun _ rs h ->
                 sel it_f h == (G.reveal rs)._1 /\
                 sel it_r h == (G.reveal rs)._2 /\
                (let ls = h (reverse_inv_vp1 p rs) in
                 trg == L.rev_acc ls._1 ls._2) /\
                 is_null (G.reveal rs)._1 = not (G.reveal b))
  = 
    elim_vrefine ((vptr it_f `star` vptr it_r) `vdep` reverse_inv_vp1 p)
                 (reverse_inv_ref p trg b);
    elim_vdep (vptr it_f `star` vptr it_r) (reverse_inv_vp1 p)

let elim_reverse_inv_vp1 #opened (p : list_param) (rs : ref p.r & ref p.r) (r_f r_r : ref p.r)
  : SteelGhost unit opened
               (reverse_inv_vp1 p rs) (fun () -> mlistN p r_f `star` mlistN p r_r)
               (requires fun _ -> rs == (r_f, r_r))
               (ensures fun h0 () h1 -> rs == (r_f, r_r) /\
                                     h0 (reverse_inv_vp1 p rs) == (sel_listN p r_f h1, sel_listN p r_r h1))
  =
    noop ();
    change_equal_slprop (reverse_inv_vp1 p rs)
                        (mlistN p r_f `star` mlistN p r_r)

inline_for_extraction
let reverse_loop_cond (p : list_param) (trg : G.erased (list (cell_t p))) it_f it_r ()
  : SteelT bool (h_exists (reverse_inv p trg it_f it_r)) (fun b -> reverse_inv p trg it_f it_r b)
  =
    (**) let gb' : G.erased (G.erased bool) = witness_exists () in
    (**) let gb  : G.erased bool = G.reveal gb' in
    (**) change_equal_slprop (reverse_inv p trg it_f it_r (G.reveal gb'))
    (**)                     (reverse_inv p trg it_f it_r gb);
    (**) let rs   = elim_reverse_inv p trg it_f it_r gb in
    (**) let gr_f = G.hide (G.reveal rs)._1 in
    (**) let gr_r = G.hide (G.reveal rs)._2 in
    let r_f = read it_f in
    (**) elim_reverse_inv_vp1 p rs r_f gr_r;
    (**) intro_reverse_inv p trg it_f it_r (not (is_null r_f)) r_f gr_r;
    return (not (is_null r_f))

inline_for_extraction
let reverse_loop_body (p : list_param) (trg : G.erased (list (cell_t p))) (it_f it_r : ref (ref p.r)) ()
  : SteelT unit (reverse_inv p trg it_f it_r true)
                (fun () -> h_exists (reverse_inv p trg it_f it_r))
  =
    (**) let rs = elim_reverse_inv p trg it_f it_r true in
    let r_f = read it_f in
    let r_r = read it_r in
    (**) elim_reverse_inv_vp1 p rs r_f r_r;
    (**) mlistN_entry_null_iff p r_f;
    let r_f' = listN_next p r_f in
    (p.cell r_f).write_next r_r;
    write it_f r_f';
    write it_r r_f;
    (**) intro_mlistN_cons p r_f r_r;
    (**) intro_reverse_inv p trg it_f it_r (not (is_null r_f')) r_f' r_f;
    (**) intro_exists (G.hide (not (is_null r_f'))) (reverse_inv p trg it_f it_r)

inline_for_extraction
let reverse (p : list_param) (r : ref p.r)
  : Steel (ref p.r)
          (mlistN p r) (fun rt -> mlistN p rt)
          (requires fun _ -> True)
          (ensures fun h0 rt h1 -> sel_listN p rt h1 == L.rev (sel_listN p r h0))
  =
    (**) let l0 : G.erased (mlistN_sel_t p r) = gget (mlistN p r) in
    (**) let trg = G.hide (L.rev l0) in
    let it_f = malloc #(ref p.r) r    in
    let it_r = malloc #(ref p.r) null in
    (**) intro_mlistN_nil p null;
    (**) intro_reverse_inv p trg it_f it_r (not (is_null r)) r null;
    (**) intro_exists (G.hide (not (is_null r))) (reverse_inv p trg it_f it_r);
    Loops.while_loop (reverse_inv p trg it_f it_r)
                     (reverse_loop_cond p trg it_f it_r)
                     (reverse_loop_body p trg it_f it_r);
    (**) let rs = elim_reverse_inv p trg it_f it_r false in
    let r_r = read it_r in
    (**) elim_reverse_inv_vp1 p rs null r_r;
    (**) elim_mlistN_nil p null;
    free it_f;
    free it_r;
    r_r
