module Learn.Steel

module L   = FStar.List.Pure
module U32 = FStar.UInt32
module Mem = Steel.Memory

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

#set-options "--fuel 0 --ifuel 0 --ide_id_info_off"

(* ~ Composition SteelBase and Tot
   ? function without side effect
 *)
let eq_test (#a : eqtype) (r1 r2 : ref a) : Steel bool
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True) (ensures fun h0 b _ -> b = (sel r1 h0 = sel r2 h0))
  = let x1 = read r1 in
    let x2 = read r2 in
    x1 = x2

let alias_test (r1 r2 : ref U32.t) : Steel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True) (ensures fun _ () h1 -> sel r1 h1 = 1ul /\ sel r2 h1 = 2ul)
  = write r1 1ul;
    write r2 2ul

let alloc_test () : Steel unit emp (fun () -> emp) (fun _ -> True) (fun _ () _ -> True)
  =
    let r = malloc #U32.t 0ul in
    let x = read r in
    (**) assert (x = 0ul);
    write r 1ul;
    let x = read r in
    (**) assert (x == 1ul);
    free r


(* -------------------------- *)

inline_for_extraction noextract noeq
type aptr_p' (t : Type) = {
  a  : Type;
  vp : a -> vprop;
  of_sel  : (r:a) -> normal (t_of (vp r)) -> GTot t;
  set_sel : (r:a) -> normal (t_of (vp r)) -> (x : t) ->
            Ghost (normal (t_of (vp r))) (requires True) (ensures fun rt -> of_sel r rt == x);
  read  : (r:a) -> Steel t (vp r) (fun _ -> vp r) (requires fun _ -> True)
                     (ensures fun h0 x h1 -> frame_equalities (vp r) h0 h1 /\ x == of_sel r (h0 (vp r)));
  write : (r:a) -> (x : t) -> Steel unit (vp r) (fun _ -> vp r) (requires fun _ -> True)
                     (ensures fun h0 () h1 -> h1 (vp r) == set_sel r (h0 (vp r)) x)
}

inline_for_extraction noextract
type aptr_p (t : Type) = p:aptr_p' t {
     forall (r:p.a) (s : normal (t_of (p.vp r))) (x0 x1 : t) . {:pattern (p.set_sel r (p.set_sel r s x0) x1)}
       p.set_sel r (p.set_sel r s x0) x1 == p.set_sel r s x1
  }  (* TODO [set_sel s (of_sel s) == s] *)


inline_for_extraction noextract noeq
type get_set_t' (c t : Type) = {
  get : c -> Tot t;
  set : c -> t -> Tot c;
}

inline_for_extraction noextract
type get_set_t (c t : Type) = p:get_set_t' c t {
     (forall (s : c) (x : t) . {:pattern (p.get (p.set s x))}
        p.get (p.set s x) == x) /\
     (forall (s : c) (x0 x1 : t) . {:pattern (p.set (p.set s x0) x1)}
        p.set (p.set s x0) x1 == p.set s x1)
  }

inline_for_extraction noextract
let aptr_of_vptr (#t : Type) : Tot (aptr_p t) = {
  a       = ref t;
  vp      = vptr;
  of_sel  = (fun r x   -> (x <: t));
  set_sel = (fun r _ x -> x);
  read    = (fun r   -> read r);
  write   = (fun r x -> write r x)
}

inline_for_extraction noextract
let aptr_of_get_set (#c #t : Type) ($p : get_set_t c t) : Tot (aptr_p t) = {
  a       = ref c;
  vp      = vptr;
  of_sel  = (fun r x   -> p.get x);
  set_sel = (fun r s x -> p.set s x);
  read    = (fun r   -> let s = read r in p.get s);
  write   = (fun r x -> let s = read r in write r (p.set s x))
}


inline_for_extraction noextract
let test_set_ptr (xp yp : aptr_p U32.t) (x : xp.a) (y : yp.a)
  : Steel unit (xp.vp x `star` yp.vp y) (fun () -> xp.vp x `star` yp.vp y)
               (requires fun _ -> True)
               (ensures fun h0 () h1 -> h1 (xp.vp x) == h0 (xp.vp x) /\
                                     h1 (yp.vp y) == yp.set_sel y (h0 (yp.vp y)) (xp.of_sel x (h0 (xp.vp x))))
  = let v = xp.read x in
    yp.write y v

(*
inline_for_extraction noextract
let rec test_set_ptr_rec (i : U32.t) (x y : aptr_t U32.t)
  : Steel unit (x.vp `star` y.vp) (fun () -> x.vp `star` y.vp)
               (requires fun _ -> True)
               (ensures fun h0 () h1 -> h1 x.vp == h0 x.vp /\
                                     h1 y.vp == y.set_sel (h0 y.vp) (x.of_sel (h0 x.vp)))
  = if i = 0ul then begin
      let v = x.read () in
      y.write v
    end else
      test_set_ptr_rec U32.(i -^ 1ul) x y
*)

type test_struct = {
  fld_a : U32.t;
  fld_b : bool
}

inline_for_extraction noextract
let test_struct_gs_fld_a : get_set_t test_struct U32.t = {
  get = (fun c -> c.fld_a);
  set = (fun c x -> {c with fld_a = x})
}

let test_set_ptr_caller () : SteelT unit emp (fun () -> emp)
  =
    let x  = malloc #U32.t 42ul in
    let ys = malloc #test_struct ({fld_a = 0ul; fld_b = false}) in
    test_set_ptr aptr_of_vptr (aptr_of_get_set test_struct_gs_fld_a) x ys;
    let i = read x in
      assert (i == 42ul);
    let i = read ys in
      assert (i == {fld_a = 42ul; fld_b = false});
    free x;
    free ys

(* ----------------------- *)
(*
assume
val int_sl ([@@@smt_fallback] n:int) : vprop

assume val int_f (n:int) : SteelT unit (int_sl n) (fun _ -> int_sl n)

let test_subcomp_dep (n:int) : SteelT unit (int_sl n) (fun _ -> int_sl n) =
  int_f (n - 1 + 1);
  int_f n


assume
val int_sl (n : nat) : Mem.slprop u#1

type int_sel_t (n : nat) : Type
  = m : nat { m <= n }

assume
val int_sel (n : nat)
  : selector (int_sel_t n) (int_sl n)

[@@__steel_reduce__]
let vint' ([@@@smt_fallback] n : nat) : vprop' =
  {
    hp  = int_sl    n;
    t   = int_sel_t n;
    sel = int_sel   n
  }

unfold let vint ([@@@smt_fallback] n : nat) : vprop =
  VUnit (vint' n)

let test_smt_fallback (n:nat)
  : SteelT unit (vint n) (fun _ -> vint (n+1-1))
  = noop ()
  
  //change_equal_slprop (vint n) (vint (n+1-1))
*)

(* ------------------------- *)

module DInv = Steel.DisposableInvariant
open Steel.FractionalPermission

[@@__reduce__]
let half = half_perm full_perm

type st_glb =
  | GIni
  | GFirst of bool

type st_loc =
  | LIni
  | LWtd of bool

#push-options "--ifuel 1"
let st_compat (gl : st_glb) (lc : bool -> st_loc) (rs : bool -> U32.t) : prop =
  (forall (p : bool) . match lc p with
                 | LIni   -> gl <> GFirst p
                 | LWtd f -> rs p <> 0ul /\ gl = GFirst (if f then p else not p)
                                       /\ (not f ==> rs (not p) <> 0ul))
#pop-options

[@@__reduce__]
unfold let entry_CS_inv_vp (r0 r1 : ref U32.t) (gl : ghost_ref st_glb) (lc0 lc1 : ghost_ref st_loc) : vprop =
  (vptrp r0 half `star` vptrp r1 half) `star`
   ghost_vptr gl `star`
  (ghost_vptrp lc0 half `star` ghost_vptrp lc1 half)

let entry_CS_inv_rfn (((f0, f1), gl), (lc0, lc1) : ((U32.t & U32.t) & st_glb) & (st_loc & st_loc)) : prop =
  st_compat gl (fun b -> if b then lc0 else lc1) (fun b -> if b then  f0  else  f1 )

[@@__reduce__]
unfold let entry_CS_inv (r0 r1 : ref U32.t) (gl : ghost_ref st_glb) (lc0 lc1 : ghost_ref st_loc) : vprop =
  entry_CS_inv_vp r0 r1 gl lc0 lc1 `vrefine` entry_CS_inv_rfn

[@@__reduce__]
unfold let entry_CS_p_vp (r : ref U32.t) (lc : ghost_ref st_loc) : vprop =
  vptrp r half `star` ghost_vptrp lc half

(* process 1 *)

[@@__reduce__]
unfold let entry_CS_p1_vp (r0 r1 : ref U32.t) (gl : ghost_ref st_glb) (lc0 lc1 : ghost_ref st_loc) =
  (vptr r0 `star` vptrp r1 half) `star` ghost_vptr gl `star` (ghost_vptr lc0 `star` ghost_vptrp lc1 half)

noextract
let entry_CS_p1_g0 #opened r0 r1 gl lc0 lc1
  : SteelAtomic unit opened
      (entry_CS_p1_vp r0 r1 gl lc0 lc1) (fun () -> entry_CS_p1_vp r0 r1 gl lc0 lc1)
      (requires fun h0      -> entry_CS_inv_rfn  (h0 (entry_CS_p1_vp r0 r1 gl lc0 lc1)))
      (ensures  fun _ () h1 -> entry_CS_inv_rfn  (h1 (entry_CS_p1_vp r0 r1 gl lc0 lc1)) /\
                            LWtd? (ghost_sel lc0 h1))
  =
    let _ = elim_vptr r0 full_perm in
    atomic_write_pt_u32 r0 1ul;
    intro_vptr r0 full_perm 1ul;

    let st_v = ghost_read gl in
    if Ghost.reveal st_v = GFirst false
    then begin
      ghost_write lc0 (LWtd   false);
      let sl1 = gget (entry_CS_p1_vp r0 r1 gl lc0 lc1) in
      assert (entry_CS_inv_rfn sl1)
    end else begin
      ghost_write gl  (GFirst true);
      ghost_write lc0 (LWtd   true);
      let sl1 = gget (entry_CS_p1_vp r0 r1 gl lc0 lc1) in
      assert (entry_CS_inv_rfn sl1)
    end


(* TODO: ALT ? *)
[@@ __steel_reduce__]
let sel_entry_CS_p_vp (#q:vprop) r lc
  (h:rmem q{FStar.Tactics.with_tactic selector_tactic (can_be_split q (entry_CS_p_vp r lc) /\ True)})
  : GTot (U32.t & st_loc)
  = h (entry_CS_p_vp r lc)

noextract
let entry_CS_p1_with_inv r0 r1 gl lc0 lc1 (iv : DInv.inv (entry_CS_inv r0 r1 gl lc0 lc1))
    (r : Type) (req : (U32.t & st_loc) -> prop) (ens : r -> (U32.t & st_loc) -> prop)
    (f : unit -> SteelAtomic r (DInv.add_inv Set.empty iv)
                   (entry_CS_p1_vp r0 r1 gl lc0 lc1)
             (fun _ -> entry_CS_p1_vp r0 r1 gl lc0 lc1)
             (requires fun h      -> entry_CS_inv_rfn (h (entry_CS_p1_vp r0 r1 gl lc0 lc1)) /\
                                  req ((sel r0 h, ghost_sel lc0 h)))
             (ensures  fun _ rt h -> entry_CS_inv_rfn (h (entry_CS_p1_vp r0 r1 gl lc0 lc1)) /\
                                  ens rt (sel r0 h, ghost_sel lc0 h)))
  : Steel r (DInv.active half iv `star` entry_CS_p_vp r0 lc0)
      (fun _ -> DInv.active half iv `star` entry_CS_p_vp r0 lc0)
      (requires fun h      -> req (sel_entry_CS_p_vp r0 lc0 h))
      (ensures  fun _ rt h -> ens rt (sel_entry_CS_p_vp r0 lc0 h))
  =
    intro_vrefine (entry_CS_p_vp r0 lc0) req;
    Set.mem_empty (Ghost.reveal (DInv.name iv));
    let res = DInv.with_invariant iv begin fun () -> (
      elim_vrefine   (entry_CS_inv_vp r0 r1 gl lc0 lc1) entry_CS_inv_rfn;
      elim_vrefine (entry_CS_p_vp r0 lc0) req;
      gather r0; ghost_gather lc0;
      let res = f () in
      share r0; ghost_share lc0;
      intro_vrefine (entry_CS_p_vp r0 lc0) (ens res);
      intro_vrefine (entry_CS_inv_vp r0 r1 gl lc0 lc1) entry_CS_inv_rfn;
      return res
      )<: SteelAtomicT r (DInv.add_inv Set.empty iv)
                   (entry_CS_inv r0 r1 gl lc0 lc1 `star`
                   (entry_CS_p_vp r0 lc0 `vrefine` req))
           (fun res -> entry_CS_inv r0 r1 gl lc0 lc1 `star`
                   (entry_CS_p_vp r0 lc0 `vrefine` (ens res)))
    end in
    elim_vrefine (entry_CS_p_vp r0 lc0) (ens res);
    return res

let entry_CS_proc_ens (res : bool) (_,lc : U32.t & st_loc) : prop
  = res ==> lc == LWtd true

noextract
let entry_CS_p0 (r0 r1 : ref U32.t) (gl : ghost_ref st_glb) (lc0 lc1 : ghost_ref st_loc)
                (iv : DInv.inv (entry_CS_inv r0 r1 gl lc0 lc1)) ()
  : SteelT  bool (DInv.active half iv `star` entry_CS_p_vp r0 lc0)
         (fun res -> DInv.active half iv `star`
                 (entry_CS_p_vp r0 lc0 `vrefine` entry_CS_proc_ens res))
  =
    entry_CS_p1_with_inv r0 r1 gl lc0 lc1 iv
      unit (fun _ -> True) (fun _ (_, lcv) -> squash (LWtd? lcv))
    begin fun () ->
      entry_CS_p1_g0 r0 r1 gl lc0 lc1
    end;
    let res = entry_CS_p1_with_inv r0 r1 gl lc0 lc1 iv
      bool (fun (_, lcv) -> squash (LWtd? lcv)) (fun b (_, lcv) -> b ==> Ghost.reveal lcv == LWtd true)
    begin fun () ->
      let g_v1 = elim_vptr r1 half in
      let v1 = atomic_read_pt_u32 r1 in
      intro_vptr r1 half g_v1;
      return (v1 = 0ul)
    end in
    intro_vrefine (entry_CS_p_vp r0 lc0) (fun (_, lcv) -> res ==> lcv == LWtd true);
    return res

(* process 2 : TODO *)

assume
val entry_CS_p1 (r0 r1 : ref U32.t) (gl : ghost_ref st_glb) (lc0 lc1 : ghost_ref st_loc)
                (iv : DInv.inv (entry_CS_inv r0 r1 gl lc0 lc1)) (_ : unit)
  : SteelT  bool (DInv.active half iv `star` entry_CS_p_vp r1 lc1)
         (fun res -> DInv.active half iv `star`
                 (entry_CS_p_vp r1 lc1 `vrefine` entry_CS_proc_ens res))


noextract
let entry_CS (r0 r1 : ref U32.t)
  : SteelT unit (vptr r0 `star` vptr r1) (fun () -> vptr r0 `star` vptr r1)
  =
    write r0 0ul;
    write r1 0ul;
    let gl  : ghost_ref st_glb = ghost_alloc GIni in
    let lc0 : ghost_ref st_loc = ghost_alloc LIni in
    let lc1 : ghost_ref st_loc = ghost_alloc LIni in
    share r0; share r1;
    ghost_share lc0; ghost_share lc1;
    intro_vrefine (entry_CS_inv_vp r0 r1 gl lc0 lc1) entry_CS_inv_rfn;
    let iv = DInv.new_inv (entry_CS_inv r0 r1 gl lc0 lc1) in
    DInv.share iv;

    let bs = par (entry_CS_p0 r0 r1 gl lc0 lc1 iv) (entry_CS_p1 r0 r1 gl lc0 lc1 iv) in
    elim_vrefine (entry_CS_p_vp r0 lc0) (entry_CS_proc_ens bs._1);
    elim_vrefine (entry_CS_p_vp r1 lc1) (entry_CS_proc_ens bs._2);

    DInv.gather iv;
    Set.mem_empty (Ghost.reveal (DInv.name iv));//TODO: Why is it necessary ?
    assert (not (DInv.mem_inv Set.empty iv));
    //assert_norm (DInv.mem_inv Set.empty iv == Set.mem (Ghost.reveal (DInv.name iv)) Set.empty);
    //assert (not (Set.mem (Ghost.reveal (DInv.name iv)) Set.empty));
    DInv.dispose iv;
    elim_vrefine (entry_CS_inv_vp r0 r1 gl lc0 lc1) entry_CS_inv_rfn;
    gather r0; gather r1;
    ghost_gather lc0; ghost_gather lc1;

    assert (not (bs._1 && bs._2)); // Mutual exclusion

    ghost_free gl;
    ghost_free lc0; ghost_free lc1

